param([switch]$Audit, [string]$Check)

$ErrorActionPreference = 'Stop'
$projectRoot = $PSScriptRoot
$executionRoot = $projectRoot
if ($projectRoot -match '[^\x00-\x7F]') {
    $hasher = [Security.Cryptography.SHA256]::Create()
    try {
        $pathBytes = [Text.Encoding]::UTF8.GetBytes($projectRoot)
        $pathKey = ([BitConverter]::ToString($hasher.ComputeHash($pathBytes))).Replace('-', '').Substring(0, 12)
    }
    finally { $hasher.Dispose() }
    $executionRoot = Join-Path ([IO.Path]::GetTempPath()) "causal-lean-$pathKey"
    if ($executionRoot -match '[^\x00-\x7F]') {
        throw 'An ASCII temporary path is required by this Windows Lean toolchain.'
    }
    if (Test-Path -LiteralPath $executionRoot) {
        $aliasItem = Get-Item -LiteralPath $executionRoot
        if ($aliasItem.LinkType -ne 'Junction' -or $aliasItem.Target -ne $projectRoot) {
            throw "The existing temporary alias does not point to this project: $executionRoot"
        }
    }
    else {
        New-Item -ItemType Junction -Path $executionRoot -Value $projectRoot | Out-Null
    }
}
$localBin = Join-Path $executionRoot '.tools\lean-4.19.0-windows\bin'
$previousPath = $env:PATH
$previousCache = $env:MATHLIB_CACHE_DIR
$previousGitCount = $env:GIT_CONFIG_COUNT
$gitConfigStart = if ($previousGitCount) { [int]$previousGitCount } else { 0 }
$gitConfigEnd = $gitConfigStart

try {
    if (Test-Path -LiteralPath (Join-Path $localBin 'lake.exe')) {
        $env:PATH = $localBin + [IO.Path]::PathSeparator + $env:PATH
    }
    $lakeCommand = Get-Command lake.exe -ErrorAction Stop
    $env:MATHLIB_CACHE_DIR = '.tools/mathlib-cache'
    # Confine Git ownership exceptions to this process and these dependency repos.
    $packagesRoot = Join-Path $executionRoot '.lake\packages'
    if (Test-Path -LiteralPath $packagesRoot) {
        foreach ($package in Get-ChildItem -LiteralPath $packagesRoot -Directory) {
            if (Test-Path -LiteralPath (Join-Path $package.FullName '.git')) {
                $physicalRepo = Join-Path $projectRoot ('.lake\packages\' + $package.Name)
                foreach ($repo in @($package.FullName, $physicalRepo) | Select-Object -Unique) {
                    [Environment]::SetEnvironmentVariable("GIT_CONFIG_KEY_$gitConfigEnd", 'safe.directory', 'Process')
                    [Environment]::SetEnvironmentVariable("GIT_CONFIG_VALUE_$gitConfigEnd", $repo.Replace('\', '/'), 'Process')
                    $gitConfigEnd++
                }
            }
        }
        $env:GIT_CONFIG_COUNT = [string]$gitConfigEnd
    }
    Push-Location -LiteralPath $executionRoot
    try {
        if ($Check) {
            & $lakeCommand.Source env lean $Check
        }
        else {
            & $lakeCommand.Source build
        }
        if ($LASTEXITCODE -ne 0) {
            throw "Lean build failed (exit code $LASTEXITCODE)."
        }
        if ($Audit) {
            & $lakeCommand.Source env lean Audit.lean
            if ($LASTEXITCODE -ne 0) {
                throw "Axiom audit failed (exit code $LASTEXITCODE)."
            }
        }
    }
    finally {
        Pop-Location
    }
}
finally {
    $env:PATH = $previousPath
    $env:MATHLIB_CACHE_DIR = $previousCache
    for ($i = $gitConfigStart; $i -lt $gitConfigEnd; $i++) {
        [Environment]::SetEnvironmentVariable("GIT_CONFIG_KEY_$i", $null, 'Process')
        [Environment]::SetEnvironmentVariable("GIT_CONFIG_VALUE_$i", $null, 'Process')
    }
    $env:GIT_CONFIG_COUNT = $previousGitCount
}
