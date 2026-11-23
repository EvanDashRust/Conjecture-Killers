param([string]$Mathlib=$env:CRYSTAL_MATHLIB,[string]$Lean=$env:CRYSTAL_LEAN)
$ErrorActionPreference='Stop'
if (-not $Mathlib) {$Mathlib=(Resolve-Path "$PSScriptRoot\..\..\find-the-newest-message-in-my\work\mathlib4").Path}
if (-not $Lean) {$Lean=(Resolve-Path "$PSScriptRoot\..\..\find-the-newest-message-in-my\work\elan\toolchains\leanprover--lean4---v4.33.1\bin\lean.exe").Path}
$cache=Join-Path $Mathlib '.lake\build\lib\lean'
$libs=@("$PSScriptRoot\proof",$cache)
Get-ChildItem (Join-Path $Mathlib '.lake\packages') -Directory | ForEach-Object {$libs+=($_.FullName+'\.lake\build\lib\lean')}
$prior=$env:LEAN_PATH
Push-Location "$PSScriptRoot\proof"
try {
  $env:LEAN_PATH=$libs -join ';'
  $version=& $Lean --version
  if ($version -notmatch 'version 4\.33\.1,') {throw 'Expected Lean 4.33.1'}
  $rev=(Get-Content "$Mathlib\.git\HEAD" -Raw).Trim()
  if ($rev -ne '0df444a360eaa60ab8c11dca51a86af692955474') {$rev=(& git -C $Mathlib rev-parse HEAD).Trim()}
  if ($rev -ne '0df444a360eaa60ab8c11dca51a86af692955474') {throw "Unexpected mathlib revision $rev"}
  $log="$PSScriptRoot\logs\lean.txt"
  @($version,"mathlib $rev","compiler $Lean","imports $env:LEAN_PATH") | Set-Content -Encoding utf8 $log
  & (Join-Path (Split-Path $Lean) 'lake.exe') --version | Tee-Object -Append -FilePath $log
  foreach ($unit in 'Upstream','Crystal','Five','Transfer') {
    $argsLean=@('-j1','-M2048','-T1500000','-o',"$unit.olean","$unit.lean")
    "lean $argsLean" | Tee-Object -Append -FilePath $log
    & $Lean @argsLean 2>&1 | Tee-Object -Append -FilePath $log
    $rc=$LASTEXITCODE
    "exit $rc" | Tee-Object -Append -FilePath $log
    if ($rc -ne 0) {exit $rc}
  }
  $receipts = Get-Content $log | Where-Object {$_ -match 'depends on axioms:'}
  if (($receipts | Measure-Object).Count -lt 20) {throw 'Missing axiom checks'}
  foreach ($line in $receipts) {
    $deps=($line -split 'depends on axioms:')[1].Trim().Trim('[',']') -split ', '
    foreach ($axiom in $deps) {
      if ($axiom -notin 'propext','Classical.choice','Quot.sound') {throw "Unexpected axiom $axiom"}
    }
  }
  $checker=Join-Path (Split-Path $Lean) 'leanchecker.exe'
  'leanchecker -v Upstream Crystal Five Transfer' | Tee-Object -Append -FilePath $log
  & $checker -v Upstream Crystal Five Transfer 2>&1 | Tee-Object -Append -FilePath $log
  $rc=$LASTEXITCODE
  "kernel replay exit $rc" | Tee-Object -Append -FilePath $log
  if ($rc -ne 0) {exit $rc}
} finally {Pop-Location; $env:LEAN_PATH=$prior}
