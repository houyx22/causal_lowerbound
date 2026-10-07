#requires -Version 7.0

$ErrorActionPreference = 'Stop'
$repositoryRoot = Split-Path -Parent $PSScriptRoot
$exportDirectory = Join-Path $repositoryRoot 'dist'
$archivePath = Join-Path $exportDirectory 'causal-lowerbound.zip'

# An explicit allowlist keeps toolchains, dependencies, and local logs out.
$relativeFiles = [Collections.Generic.List[string]]::new()
$rootFiles = @(
    'README.md',
    '.gitignore',
    '.gitattributes',
    'LowerBound_Complete_Revised.tex',
    'LowerBound_Complete_Revised.pdf',
    'formalization/.gitignore',
    'formalization/README.md',
    'formalization/CausalLowerbound.lean',
    'formalization/Audit.lean',
    'formalization/Build.ps1',
    'formalization/lean-toolchain',
    'formalization/lakefile.toml',
    'formalization/lake-manifest.json'
)
foreach ($relativePath in $rootFiles) {
    $fullPath = Join-Path $repositoryRoot $relativePath
    if (-not (Test-Path -LiteralPath $fullPath -PathType Leaf)) {
        throw "Required publication file is missing: $relativePath"
    }
    $relativeFiles.Add($relativePath)
}

$directoryRules = @(
    @{ Path = 'formalization/CausalLowerbound'; Extension = '.lean' },
    @{ Path = 'docs'; Extension = '.md' },
    @{ Path = 'scripts'; Extension = '.ps1' },
    @{ Path = '.github/workflows'; Extension = '.yml' }
)
foreach ($rule in $directoryRules) {
    $sourceDirectory = Join-Path $repositoryRoot $rule.Path
    foreach ($source in Get-ChildItem -LiteralPath $sourceDirectory -File -Recurse) {
        if ($source.Extension -eq $rule.Extension) {
            $relativePath = [IO.Path]::GetRelativePath($repositoryRoot, $source.FullName).Replace('\', '/')
            $relativeFiles.Add($relativePath)
        }
    }
}

$publicationFiles = @($relativeFiles | Sort-Object -Unique)
New-Item -ItemType Directory -Path $exportDirectory -Force | Out-Null
$archiveStream = [IO.File]::Open($archivePath, [IO.FileMode]::Create, [IO.FileAccess]::ReadWrite)
try {
    $archive = [IO.Compression.ZipArchive]::new($archiveStream, [IO.Compression.ZipArchiveMode]::Create)
    try {
        foreach ($relativePath in $publicationFiles) {
            $sourcePath = Join-Path $repositoryRoot $relativePath
            [IO.Compression.ZipFileExtensions]::CreateEntryFromFile(
                $archive,
                $sourcePath,
                "causal-lowerbound/$relativePath",
                [IO.Compression.CompressionLevel]::Optimal
            ) | Out-Null
        }
    }
    finally {
        $archive.Dispose()
    }
}
finally {
    $archiveStream.Dispose()
}

$archiveInfo = Get-Item -LiteralPath $archivePath
[pscustomobject]@{
    Archive = $archiveInfo.FullName
    Files = $publicationFiles.Count
    Bytes = $archiveInfo.Length
    SHA256 = (Get-FileHash -LiteralPath $archivePath -Algorithm SHA256).Hash
}
