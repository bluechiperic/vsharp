#!/usr/bin/env bash
# Build self-contained vsharpc packages for every supported RID.
#
#   ./build/package.sh                  # test, then every archive this machine can produce
#   ./build/package.sh --skip-test      # packaging only
#   ./build/package.sh --rid linux-x64  # one runtime (repeatable)
#   ./build/package.sh --pkg-only artifacts/vsharpc-0.1.0-osx-arm64.tar.gz
#
# Windows .zip, macOS/Linux .tar.gz, and on Windows a .msi (WiX links msi.dll).
# Linux .deb and .rpm, a framework-dependent `dotnet tool` nupkg, a Homebrew
# formula, and a winget manifest land in artifacts/. SHA256SUMS covers them.
set -euo pipefail

ROOT=$(cd "$(dirname "$0")/.." && pwd)
cd "$ROOT"

export DOTNET_CLI_TELEMETRY_OPTOUT=1
export DOTNET_NOLOGO=1

VERSION="${VERSION:-}"
if [[ -z "$VERSION" && "${GITHUB_REF:-}" == refs/tags/v* ]]; then
  VERSION="${GITHUB_REF#refs/tags/v}"
fi
VERSION="${VERSION:-0.1.0}"

SKIP_TEST=0
RIDS=()
PKG_ONLY=()
while [[ $# -gt 0 ]]; do
  case "$1" in
    --skip-test) SKIP_TEST=1; shift ;;
    --rid) RIDS+=("$2"); shift 2 ;;
    --pkg-only) PKG_ONLY+=("$2"); shift 2 ;;
    -h|--help)
      sed -n '2,12p' "$0"
      exit 0
      ;;
    *) echo "unknown argument: $1" >&2; exit 2 ;;
  esac
done

ALL_RIDS=(win-x64 win-arm64 osx-x64 osx-arm64 linux-x64 linux-arm64)
if [[ ${#RIDS[@]} -eq 0 ]]; then RIDS=("${ALL_RIDS[@]}"); fi

msi_version() {
  if [[ "$1" =~ ^([0-9]+)\.([0-9]+)\.([0-9]+) ]]; then
    echo "${BASH_REMATCH[1]}.${BASH_REMATCH[2]}.${BASH_REMATCH[3]}.0"
  else
    echo "0.0.0.0"
  fi
}

deb_version() { echo "$1" | sed 's/-/~/g'; }

host_rid() {
  local os arch
  os=$(uname -s)
  arch=$(uname -m)
  case "$os-$arch" in
    Linux-x86_64) echo linux-x64 ;;
    Linux-aarch64|Linux-arm64) echo linux-arm64 ;;
    Darwin-arm64) echo osx-arm64 ;;
    Darwin-x86_64) echo osx-x64 ;;
    MINGW*|MSYS*|CYGWIN*)
      case "$arch" in aarch64|arm64) echo win-arm64 ;; *) echo win-x64 ;; esac
      ;;
    *) echo "" ;;
  esac
}

sha256_file() {
  if command -v sha256sum >/dev/null 2>&1; then sha256sum "$1" | awk '{print $1}'
  elif command -v shasum >/dev/null 2>&1; then shasum -a 256 "$1" | awk '{print $1}'
  else python3 -c 'import hashlib,sys; print(hashlib.sha256(open(sys.argv[1],"rb").read()).hexdigest())' "$1"
  fi
}

need_native() {
  case "$1" in
    linux-*) [[ -f "$2/libz3.so" ]] ;;
    osx-*) [[ -f "$2/libz3.dylib" ]] ;;
    win-x64) [[ -f "$2/libz3.dll" ]] ;;
    # Z3 4.12.2 publishes no Windows ARM64 binary, and the tag does not build with mingw-clang.
    win-arm64) return 0 ;;
    *) return 1 ;;
  esac
}

# ---- macOS .pkg from an existing tarball (pkgbuild exists only on macOS) ----
if [[ ${#PKG_ONLY[@]} -gt 0 ]]; then
  command -v pkgbuild >/dev/null 2>&1 || { echo "pkgbuild is required (macOS)" >&2; exit 1; }
  mkdir -p "$ROOT/artifacts"
  for tarball in "${PKG_ONLY[@]}"; do
    base=$(basename "$tarball" .tar.gz)
    if [[ ! "$base" =~ ^vsharpc-(.+)-(osx-arm64|osx-x64)$ ]]; then
      echo "expected vsharpc-<version>-osx-arm64.tar.gz, got $tarball" >&2
      exit 1
    fi
    ver="${BASH_REMATCH[1]}"
    rid="${BASH_REMATCH[2]}"
    stage=$(mktemp -d)
    mkdir -p "$stage/root/usr/local/lib/vsharpc" "$stage/root/usr/local/bin" "$stage/src"
    tar -xzf "$tarball" -C "$stage/src"
    src=$(echo "$stage/src"/*)
    cp -a "$src"/. "$stage/root/usr/local/lib/vsharpc/"
    ln -s ../lib/vsharpc/vsharpc "$stage/root/usr/local/bin/vsharpc"
    out="$ROOT/artifacts/vsharpc-${ver}-${rid}.pkg"
    pkgbuild --root "$stage/root" --identifier com.github.bluechiperic.vsharpc \
      --version "$(deb_version "$ver")" --install-location / "$out"
    rm -rf "$stage"
    echo "wrote $out"
  done
  exit 0
fi

fetch_args=()
  for rid in "${RIDS[@]}"; do
    case "$rid" in
      linux-arm64) fetch_args+=(--build-linux-arm64) ;;
    esac
  done
bash "$ROOT/build/fetch-z3.sh" "${fetch_args[@]}"

if [[ "$SKIP_TEST" == 0 ]]; then
  dotnet test "$ROOT/VSharp.sln" -c Release --nologo
fi

OUT="$ROOT/artifacts"
rm -rf "$OUT"
mkdir -p "$OUT"

write_notices() {
  local dir=$1
  cp -f "$ROOT/LICENSE" "$dir/LICENSE"
  if [[ -f "$ROOT/build/.cache/z3/LICENSE-Z3.txt" ]]; then
    cp -f "$ROOT/build/.cache/z3/LICENSE-Z3.txt" "$dir/LICENSE-Z3.txt"
  fi
  cat > "$dir/THIRD-PARTY-NOTICES.txt" <<'EOF'
This vsharpc distribution includes:

- The .NET runtime, copyright .NET Foundation and contributors, MIT license.
  https://github.com/dotnet/runtime

- Z3 4.12.2, copyright Microsoft Corporation, MIT license.
  https://github.com/Z3Prover/z3
  win-x64, linux-x64, osx-x64, and osx-arm64 natives are the official release binaries.
  linux-arm64 and win-arm64, when present, are built from the z3-4.12.2 tag because
  that release has no official archive for them. The Windows x64 build ships the
  Visual C++ runtime DLLs that the official Z3 archive places beside libz3.dll.

- ILGPU, used by VSharp.Runtime, MIT license.
  https://github.com/m4rs-mt/ILGPU
EOF
}

install_blurb() {
  local rid=$1 dir=$2
  cat > "$dir/INSTALL.txt" <<EOF
vsharpc ${VERSION} (${rid})

The folder is a self-contained build. It does not need a .NET install.
Put it on PATH:

  export PATH="\$PWD:\$PATH"     # macOS and Linux, from this folder
  set PATH=%CD%;%PATH%           # Windows cmd, from this folder

Then:  vsharpc explain TN3001
       vsharpc check hello.vs

Z3 4.12.2 is included (libz3) on every RID except win-arm64. Verification needs that library.
linux-x64 is the official glibc 2.31 build (glibc 2.29 or newer, plus libstdc++6).
linux-arm64 is built from the same tag and needs glibc 2.38 or newer; see GLIBC.txt.
Windows x64 needs Windows 10 or newer. The Visual C++ DLLs Z3 imports are in this folder.
Windows ARM64 has no libz3 in this package. See NOTICE.txt. The win-x64 build runs under emulation.
macOS needs 11 or newer. libz3 links only libSystem and libc++, which the system provides.

Signing and notarization are not applied. Compare the download with SHA256SUMS.
EOF
  if [[ -f "$ROOT/build/.cache/z3/linux-arm64/GLIBC" && "$rid" == linux-arm64 ]]; then
    echo "linux-arm64 libz3 maximum glibc symbol: $(cat "$ROOT/build/.cache/z3/linux-arm64/GLIBC")" > "$dir/GLIBC.txt"
  fi
}

publish_rid() {
  local rid=$1
  local dest="$OUT/publish/$rid"
  echo "publishing $rid"
  dotnet publish "$ROOT/src/VSharp.Compiler/VSharp.Compiler.csproj" \
    -c Release -r "$rid" --self-contained true \
    -p:Version="$VERSION" \
    -p:DebugType=none -p:DebugSymbols=false \
    -p:InvariantGlobalization=true \
    -o "$dest"
  if ! need_native "$rid" "$dest"; then
    echo "publish for $rid did not include libz3" >&2
    exit 1
  fi
  write_notices "$dest"
  install_blurb "$rid" "$dest"
  if [[ "$rid" == win-arm64 && ! -f "$dest/libz3.dll" ]]; then
    cat > "$dest/NOTICE.txt" <<'EOF'
Z3 4.12.2 has no official Windows ARM64 binary. The z3-4.12.2 tag also fails to
build with the current mingw-clang toolchain (Clang diagnoses template code that
GCC never instantiates). This package can format, print signatures, and explain
diagnostics. `check` and `build` load libz3 and will not verify here.

To verify on a Windows ARM machine, install the win-x64 package. Windows runs
that build under emulation.
EOF
  fi
}

archive_name() { echo "vsharpc-${VERSION}-$1"; }

make_tarball() {
  local rid=$1
  local name
  name=$(archive_name "$rid")
  mkdir -p "$OUT/stage"
  rm -rf "$OUT/stage/$name"
  mkdir -p "$OUT/stage/$name"
  cp -a "$OUT/publish/$rid"/. "$OUT/stage/$name/"
  tar -C "$OUT/stage" -czf "$OUT/${name}.tar.gz" "$name"
  echo "wrote $OUT/${name}.tar.gz"
}

make_zip() {
  local rid=$1
  local name
  name=$(archive_name "$rid")
  mkdir -p "$OUT/stage"
  rm -rf "$OUT/stage/$name"
  mkdir -p "$OUT/stage/$name"
  cp -a "$OUT/publish/$rid"/. "$OUT/stage/$name/"
  (cd "$OUT/stage" && zip -qr "$OUT/${name}.zip" "$name")
  echo "wrote $OUT/${name}.zip"
}

# Highest GLIBC_x.y.z required by the apphost and libz3, as a Debian version (2.29).
max_glibc() {
  local dir=$1 best="2.17"
  local objdump=objdump
  command -v objdump >/dev/null 2>&1 || return 0
  local f sym
  for f in "$dir/vsharpc" "$dir/libz3.so"; do
    [[ -f "$f" ]] || continue
    while IFS= read -r sym; do
      sym=${sym#GLIBC_}
      if "$PY" -c 'import sys; a=sys.argv[1].split("."); b=sys.argv[2].split(".");
pad=max(len(a),len(b));
print(tuple(map(int,(a+[0]*pad)[:pad])) > tuple(map(int,(b+[0]*pad)[:pad])))' "$sym" "$best" | grep -q True; then
        best=$sym
      fi
    done < <(objdump -T "$f" 2>/dev/null | grep -oE 'GLIBC_[0-9.]+' || true)
  done
  echo "$best"
}

if command -v python3 >/dev/null 2>&1; then PY=python3; else PY=python; fi

make_deb() {
  local rid=$1
  command -v dpkg-deb >/dev/null 2>&1 || { echo "skipping .deb (dpkg-deb not installed)"; return 0; }
  local arch glibc
  case "$rid" in
    linux-x64) arch=amd64 ;;
    linux-arm64) arch=arm64 ;;
    *) return 0 ;;
  esac
  glibc=$(max_glibc "$OUT/publish/$rid")
  local ver stage
  ver=$(deb_version "$VERSION")
  stage=$(mktemp -d)
  mkdir -p "$stage/usr/lib/vsharpc" "$stage/usr/bin" "$stage/usr/share/doc/vsharpc" "$stage/DEBIAN"
  cp -a "$OUT/publish/$rid"/. "$stage/usr/lib/vsharpc/"
  ln -s ../lib/vsharpc/vsharpc "$stage/usr/bin/vsharpc"
  cp -f "$stage/usr/lib/vsharpc/LICENSE" "$stage/usr/share/doc/vsharpc/copyright"
  local depends="libc6 (>= ${glibc}), libgcc-s1, zlib1g"
  if objdump -p "$OUT/publish/$rid/vsharpc" 2>/dev/null | grep -q 'NEEDED.*libstdc++' \
     || objdump -p "$OUT/publish/$rid/libz3.so" 2>/dev/null | grep -q 'NEEDED.*libstdc++'; then
    depends="$depends, libstdc++6"
  fi
  cat > "$stage/DEBIAN/control" <<EOF
Package: vsharpc
Version: ${ver}
Section: devel
Priority: optional
Architecture: ${arch}
Maintainer: VSharp Project <https://github.com/bluechiperic/vsharp>
Homepage: https://github.com/bluechiperic/vsharp
Depends: ${depends}
Description: V# compiler
 Proves function contracts and emits .NET IL.
 Self-contained build for ${rid}. Z3 4.12.2 is included.
EOF
  local deb="$OUT/vsharpc_${ver}_${arch}.deb"
  dpkg-deb --root-owner-group --build "$stage" "$deb"
  rm -rf "$stage"
  echo "wrote $deb"
}

make_rpm() {
  local rid=$1
  command -v rpmbuild >/dev/null 2>&1 || { echo "skipping .rpm (rpmbuild not installed)"; return 0; }
  local arch
  case "$rid" in
    linux-x64) arch=x86_64 ;;
    linux-arm64) arch=aarch64 ;;
    *) return 0 ;;
  esac
  local ver top spec rpm
  ver=$(deb_version "$VERSION")
  top=$(mktemp -d)
  mkdir -p "$top"/{BUILD,RPMS,SOURCES,SPECS,SRPMS} "$top/SOURCES/payload"
  cp -a "$OUT/publish/$rid"/. "$top/SOURCES/payload/"
  spec="$top/SPECS/vsharpc.spec"
  cat > "$spec" <<EOF
Name: vsharpc
Version: ${ver}
Release: 1
Summary: V# compiler
License: Apache-2.0
URL: https://github.com/bluechiperic/vsharp
BuildArch: ${arch}
AutoReqProv: no
Requires: glibc, libgcc, zlib
$(if objdump -p "$OUT/publish/$rid/libz3.so" 2>/dev/null | grep -q 'NEEDED.*libstdc++' \
    || objdump -p "$OUT/publish/$rid/vsharpc" 2>/dev/null | grep -q 'NEEDED.*libstdc++'; then
     echo "Requires: libstdc++"
   fi)

%define __os_install_post %{nil}
%define debug_package %{nil}

%description
Proves function contracts and emits .NET IL. Self-contained build for ${rid}.
Z3 4.12.2 is included.

%install
mkdir -p %{buildroot}/usr/lib/vsharpc %{buildroot}/usr/bin
cp -a %{_sourcedir}/payload/. %{buildroot}/usr/lib/vsharpc/
ln -s ../lib/vsharpc/vsharpc %{buildroot}/usr/bin/vsharpc

%files
/usr/lib/vsharpc
/usr/bin/vsharpc
EOF
  # rpm refuses a BuildArch the host is not "compatible" with. A one-line rpmrc
  # lets an x64 machine pack the aarch64 payload it already cross-published.
  local rc_args=() rpm_host rc
  rpm_host=$(rpm --eval '%{_host_cpu}')
  if [[ "$arch" != "$rpm_host" ]]; then
    rc=$(mktemp)
    cp /usr/lib/rpm/rpmrc "$rc"
    printf '\nbuildarch_compat: %s: %s noarch\n' "$rpm_host" "$arch" >> "$rc"
    rc_args=(--rcfile "/usr/lib/rpm/rpmrc:$rc")
  fi
  rpmbuild "${rc_args[@]}" -bb --define "_topdir $top" "$spec"
  rpm=$(find "$top/RPMS" -name '*.rpm' | head -1)
  cp -f "$rpm" "$OUT/vsharpc-${ver}-1.${arch}.rpm"
  rm -rf "$top"
  echo "wrote $OUT/vsharpc-${ver}-1.${arch}.rpm"
}

make_msi() {
  local rid=$1
  # WiX binds the MSI through msi.dll. That library exists only on Windows, including v5.
  case "$(uname -s)" in
    MINGW*|MSYS*|CYGWIN*) ;;
    *) echo "skipping .msi for $rid (WiX needs Windows; .github/workflows/release.yml builds it on windows-latest)"; return 0 ;;
  esac
  local wix="$ROOT/build/.tools/wix.exe"
  if [[ ! -x "$wix" ]]; then
    dotnet tool install wix --tool-path "$ROOT/build/.tools" --version 5.0.2
  fi
  local arch publish
  case "$rid" in
    win-x64) arch=x64 ;;
    win-arm64) arch=arm64 ;;
    *) return 0 ;;
  esac
  publish=$(cygpath -w "$OUT/publish/$rid")
  local ver out
  ver=$(msi_version "$VERSION")
  out="$OUT/vsharpc-${VERSION}-${rid}.msi"
  "$wix" build "$(cygpath -w "$ROOT/packaging/wix/vsharpc.wxs")" \
    -arch "$arch" \
    -d "Version=$ver" \
    -d "PublishDir=$publish" \
    -o "$(cygpath -w "$out")"
  echo "wrote $out"
}

for rid in "${RIDS[@]}"; do
  publish_rid "$rid"
  case "$rid" in
    win-*) make_zip "$rid"; make_msi "$rid" ;;
    linux-*) make_tarball "$rid"; make_deb "$rid"; make_rpm "$rid" ;;
    osx-*) make_tarball "$rid" ;;
  esac
done

echo "packing dotnet tool"
dotnet pack "$ROOT/src/VSharp.Compiler/VSharp.Compiler.csproj" -c Release \
  -p:Version="$VERSION" -p:DebugType=none -p:DebugSymbols=false \
  -o "$OUT"
tool=$(find "$OUT" -maxdepth 1 -name 'vsharpc.*.nupkg' | head -1)
if ! unzip -l "$tool" | grep -q 'libz3'; then
  echo "tool package $tool does not contain libz3; embedding staged natives" >&2
  embed=$(mktemp -d)
  unzip -q "$tool" -d "$embed"
  tfm=$(find "$embed/tools" -mindepth 1 -maxdepth 1 -type d | head -1)
  any="$tfm/any"
  mkdir -p "$any"
  cp -a "$ROOT/build/.cache/z3/staged/." "$any/runtimes/"
  if [[ ! -f "$any/Microsoft.Z3.dll" ]]; then
    cp -f "$ROOT/build/.cache/z3/managed/Microsoft.Z3.dll" "$any/Microsoft.Z3.dll"
  fi
  rm -f "$tool"
  (cd "$embed" && zip -qr "$tool" .)
  rm -rf "$embed"
  unzip -l "$tool" | grep -q 'libz3' || { echo "failed to embed libz3 in the tool package" >&2; exit 1; }
fi

# Homebrew formula and winget manifest, filled with the checksums of this run.
mkdir -p "$OUT/homebrew" "$OUT/winget"
sha_of() {
  local f="$OUT/$1"
  if [[ -f "$f" ]]; then sha256_file "$f"; else echo "unavailable"; fi
}
ver_deb=$(deb_version "$VERSION")
cat > "$OUT/homebrew/vsharpc.rb" <<EOF
# Generated by build/package.sh. Copy into a Homebrew tap the maintainer owns
# (for example github.com/bluechiperic/homebrew-vsharp) and \`brew tap\` that repo.
# Releases are unsigned. Bottling and notarization are the tap owner's step.
class Vsharpc < Formula
  desc "V# compiler: prove function contracts and emit .NET IL"
  homepage "https://github.com/bluechiperic/vsharp"
  version "${VERSION}"
  license "Apache-2.0"

  on_macos do
    on_arm do
      url "https://github.com/bluechiperic/vsharp/releases/download/v${VERSION}/vsharpc-${VERSION}-osx-arm64.tar.gz"
      sha256 "$(sha_of "vsharpc-${VERSION}-osx-arm64.tar.gz")"
    end
    on_intel do
      url "https://github.com/bluechiperic/vsharp/releases/download/v${VERSION}/vsharpc-${VERSION}-osx-x64.tar.gz"
      sha256 "$(sha_of "vsharpc-${VERSION}-osx-x64.tar.gz")"
    end
  end

  on_linux do
    on_arm do
      url "https://github.com/bluechiperic/vsharp/releases/download/v${VERSION}/vsharpc-${VERSION}-linux-arm64.tar.gz"
      sha256 "$(sha_of "vsharpc-${VERSION}-linux-arm64.tar.gz")"
    end
    on_intel do
      url "https://github.com/bluechiperic/vsharp/releases/download/v${VERSION}/vsharpc-${VERSION}-linux-x64.tar.gz"
      sha256 "$(sha_of "vsharpc-${VERSION}-linux-x64.tar.gz")"
    end
  end

  def install
    libexec.install Dir["*"]
    bin.install_symlink libexec/"vsharpc"
  end

  test do
    system bin/"vsharpc", "explain"
  end
end
EOF

cat > "$OUT/winget/VSharp.vsharpc.yaml" <<EOF
# Generated by build/package.sh. Submit to microsoft/winget-pkgs after validating
# with \`winget validate\`. The zip is unsigned; winget may require a signed installer
# before the PR is accepted. The portable installer keeps the files beside vsharpc.exe.
PackageIdentifier: VSharp.vsharpc
PackageVersion: ${VERSION}
PackageLocale: en-US
Publisher: VSharp
PackageName: vsharpc
License: Apache-2.0
ShortDescription: V# compiler that proves function contracts and emits .NET IL
PackageUrl: https://github.com/bluechiperic/vsharp
Installers:
  - Architecture: x64
    InstallerType: zip
    NestedInstallerType: portable
    NestedInstallerFiles:
      - RelativeFilePath: vsharpc-${VERSION}-win-x64\\vsharpc.exe
        PortableCommandAlias: vsharpc
    InstallerUrl: https://github.com/bluechiperic/vsharp/releases/download/v${VERSION}/vsharpc-${VERSION}-win-x64.zip
    InstallerSha256: $(sha_of "vsharpc-${VERSION}-win-x64.zip")
  - Architecture: arm64
    InstallerType: zip
    NestedInstallerType: portable
    NestedInstallerFiles:
      - RelativeFilePath: vsharpc-${VERSION}-win-arm64\\vsharpc.exe
        PortableCommandAlias: vsharpc
    InstallerUrl: https://github.com/bluechiperic/vsharp/releases/download/v${VERSION}/vsharpc-${VERSION}-win-arm64.zip
    InstallerSha256: $(sha_of "vsharpc-${VERSION}-win-arm64.zip")
ManifestType: singleton
ManifestVersion: 1.6.0
EOF

host=$(host_rid)
for rid in "${RIDS[@]}"; do
  [[ "$rid" == "$host" ]] || continue
  bin="$OUT/publish/$rid/vsharpc"
  [[ -f "$bin" ]] || bin="$OUT/publish/$rid/vsharpc.exe"
  [[ -f "$bin" ]] || { echo "no packaged binary to smoke-test for $rid" >&2; exit 1; }
  echo "smoke test $bin"
  "$bin" explain TN3001 >/dev/null
  "$bin" check "$ROOT/build/smoke/min.vs"
  "$bin" check "$ROOT/samples/search.vs"
  smoke_out=$(mktemp -d)
  "$bin" build "$ROOT/build/smoke/min.vs" -o "$smoke_out"
  [[ -f "$smoke_out/Smoke.dll" ]] || { echo "build did not emit Smoke.dll" >&2; exit 1; }
  rm -rf "$smoke_out"
  echo "smoke test passed ($rid)"
done

(
  cd "$OUT"
  : > SHA256SUMS
  find . -type f ! -name SHA256SUMS ! -path './publish/*' ! -path './stage/*' | sort | while IFS= read -r f; do
    f=${f#./}
    echo "$(sha256_file "$f")  $f" >> SHA256SUMS
  done
)
echo "artifacts:"
find "$OUT" -type f ! -path '*/publish/*' ! -path '*/stage/*' | sort
