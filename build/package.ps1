# Runs build/package.sh. Git for Windows supplies bash on a typical Windows install,
# and GitHub Actions' windows-latest image does too. Arguments are forwarded
# (--rid win-x64, --skip-test, --pkg-only is macOS-only).
$ErrorActionPreference = 'Stop'
$root = Split-Path -Parent $MyInvocation.MyCommand.Path
$candidates = @(
    "$env:ProgramFiles\Git\bin\bash.exe",
    "${env:ProgramFiles(x86)}\Git\bin\bash.exe"
)
$bash = $candidates | Where-Object { $_ -and (Test-Path $_) } | Select-Object -First 1
if (-not $bash) {
    $cmd = Get-Command bash -ErrorAction SilentlyContinue
    if ($cmd) { $bash = $cmd.Source }
}
if (-not $bash) {
    Write-Error "package.ps1 needs bash to run build/package.sh. Install Git for Windows, or run bash build/package.sh."
}
& $bash "$root/package.sh" @args
exit $LASTEXITCODE
