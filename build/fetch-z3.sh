#!/usr/bin/env bash
# Download official Z3 4.12.2 binaries and pack them as the local NuGet package VSharp.Z3.
#
# The Microsoft.Z3 4.12.2 package on nuget.org ships an x64-only managed DLL and native
# libraries for win-x64 and osx-x64 only. This script uses the AnyCPU managed DLL from the
# official Linux archive and the official natives for win-x64, linux-x64, osx-x64, and
# osx-arm64. linux-arm64 has no official 4.12.2 archive; pass --build-linux-arm64 to
# compile it from the z3-4.12.2 tag. win-arm64 has no official binary either, and that
# tag does not build with mingw-clang, so no Windows ARM64 libz3 is packed.
set -euo pipefail

ROOT=$(cd "$(dirname "$0")/.." && pwd)
CACHE="$ROOT/build/.cache/z3"
DOWNLOADS="$CACHE/downloads"
STAGED="$CACHE/staged"
NUPKG_DIR="$ROOT/build/nugets"
Z3_TAG="z3-4.12.2"
Z3_VERSION="4.12.2"
BASE_URL="https://github.com/Z3Prover/z3/releases/download/${Z3_TAG}"

BUILD_LINUX_ARM64=0
for arg in "$@"; do
  case "$arg" in
    --build-linux-arm64) BUILD_LINUX_ARM64=1 ;;
    -h|--help)
      echo "usage: build/fetch-z3.sh [--build-linux-arm64]"
      exit 0
      ;;
    *) echo "unknown argument: $arg" >&2; exit 2 ;;
  esac
done

if command -v python3 >/dev/null 2>&1; then PY=python3
elif command -v python >/dev/null 2>&1; then PY=python
else echo "python3 is required" >&2; exit 1
fi

sha256_file() {
  if command -v sha256sum >/dev/null 2>&1; then sha256sum "$1" | awk '{print $1}'
  elif command -v shasum >/dev/null 2>&1; then shasum -a 256 "$1" | awk '{print $1}'
  else "$PY" -c 'import hashlib,sys; print(hashlib.sha256(open(sys.argv[1],"rb").read()).hexdigest())' "$1"
  fi
}

download() {
  local url=$1 dest=$2 sha=$3
  if [[ -f "$dest" ]] && [[ "$(sha256_file "$dest")" == "$sha" ]]; then
    echo "cached $(basename "$dest")"
    return
  fi
  echo "downloading $(basename "$dest")"
  mkdir -p "$(dirname "$dest")"
  curl -fL --retry 5 --retry-delay 2 -o "$dest.partial" "$url"
  local got
  got=$(sha256_file "$dest.partial")
  if [[ "$got" != "$sha" ]]; then
    echo "checksum mismatch for $dest" >&2
    echo "  expected $sha" >&2
    echo "  got      $got" >&2
    exit 1
  fi
  mv "$dest.partial" "$dest"
}

# kind <file> prints pe-i386, pe-x64, pe-arm64, elf-x64, elf-arm64, macho-x64, or macho-arm64.
kind() {
  "$PY" -c '
import sys
path = sys.argv[1]
with open(path, "rb") as f:
    magic = f.read(4)
    if magic[:2] == b"MZ":
        f.seek(0x3C)
        pe = int.from_bytes(f.read(4), "little")
        f.seek(pe)
        if f.read(4) != b"PE\0\0":
            sys.exit("not a PE file: " + path)
        machine = int.from_bytes(f.read(2), "little")
        print({0x14C: "pe-i386", 0x8664: "pe-x64", 0xAA64: "pe-arm64"}.get(machine, hex(machine)))
    elif magic == b"\x7fELF":
        f.seek(18)
        mach = int.from_bytes(f.read(2), "little")
        print({62: "elf-x64", 183: "elf-arm64"}.get(mach, hex(mach)))
    elif magic in (b"\xcf\xfa\xed\xfe", b"\xfe\xed\xfa\xcf"):
        order = "big" if magic == b"\xfe\xed\xfa\xcf" else "little"
        f.seek(4)
        cputype = int.from_bytes(f.read(4), order) & 0xFF
        # ABI64 bit is in the high byte; the low byte is 7 (x86_64) or 12 (arm64).
        print({7: "macho-x64", 12: "macho-arm64"}.get(cputype, hex(cputype)))
    else:
        sys.exit("unrecognized binary: " + path)
' "$1"
}

expect_kind() {
  local file=$1 expected=$2
  local got
  got=$(kind "$file")
  if [[ "$got" != "$expected" ]]; then
    echo "$file is $got, expected $expected" >&2
    exit 1
  fi
}

stage_native() {
  local rid=$1
  shift
  mkdir -p "$STAGED/$rid/native"
  cp -f "$@" "$STAGED/$rid/native/"
}

mkdir -p "$DOWNLOADS"
rm -rf "$STAGED"
mkdir -p "$STAGED"

download "$BASE_URL/z3-${Z3_VERSION}-x64-glibc-2.31.zip" \
  "$DOWNLOADS/z3-linux-x64.zip" \
  "a198851a7403d8b25bab920bd4a4792efe1af5c28a5a932d840af0472d3a83eb"
download "$BASE_URL/z3-${Z3_VERSION}-x64-win.zip" \
  "$DOWNLOADS/z3-win-x64.zip" \
  "ea33132e4531dbdc2c98b5f3c01257ca2f954e0f9c9115e63ea4e2530550e1d4"
download "$BASE_URL/z3-${Z3_VERSION}-x64-osx-10.16.zip" \
  "$DOWNLOADS/z3-osx-x64.zip" \
  "7f5ed527c022683d663108cdd00a2c89f43ae231b26fe7baf8b0b89bbf7d2aa7"
download "$BASE_URL/z3-${Z3_VERSION}-arm64-osx-11.0.zip" \
  "$DOWNLOADS/z3-osx-arm64.zip" \
  "2509f1a5250c70679347b3878b980a42640cd0b603bc87716f991d078b5a5959"

extract_one() {
  local zip=$1 inner=$2 dest=$3
  unzip -qo -j "$zip" "$inner" -d "$(dirname "$dest")"
  local base
  base=$(basename "$inner")
  if [[ "$(dirname "$dest")/$(basename "$dest")" != "$(dirname "$dest")/$base" ]]; then
    mv -f "$(dirname "$dest")/$base" "$dest"
  fi
}

MANAGED="$CACHE/managed"
mkdir -p "$MANAGED"
extract_one "$DOWNLOADS/z3-linux-x64.zip" "z3-${Z3_VERSION}-x64-glibc-2.31/bin/Microsoft.Z3.dll" "$MANAGED/Microsoft.Z3.dll"
extract_one "$DOWNLOADS/z3-linux-x64.zip" "z3-${Z3_VERSION}-x64-glibc-2.31/bin/Microsoft.Z3.xml" "$MANAGED/Microsoft.Z3.xml"
extract_one "$DOWNLOADS/z3-linux-x64.zip" "z3-${Z3_VERSION}-x64-glibc-2.31/LICENSE.txt" "$CACHE/LICENSE-Z3.txt"
expect_kind "$MANAGED/Microsoft.Z3.dll" pe-i386

extract_one "$DOWNLOADS/z3-linux-x64.zip" "z3-${Z3_VERSION}-x64-glibc-2.31/bin/libz3.so" "$CACHE/linux-x64-libz3.so"
expect_kind "$CACHE/linux-x64-libz3.so" elf-x64
if command -v patchelf >/dev/null 2>&1; then patchelf --set-soname libz3.so "$CACHE/linux-x64-libz3.so" || true; fi
mkdir -p "$STAGED/linux-x64/native"
cp -f "$CACHE/linux-x64-libz3.so" "$STAGED/linux-x64/native/libz3.so"

WIN_TMP="$CACHE/win-x64-bin"
mkdir -p "$WIN_TMP"
for f in libz3.dll msvcp140.dll msvcp140_1.dll msvcp140_2.dll vcruntime140.dll vcruntime140_1.dll; do
  extract_one "$DOWNLOADS/z3-win-x64.zip" "z3-${Z3_VERSION}-x64-win/bin/$f" "$WIN_TMP/$f"
done
expect_kind "$WIN_TMP/libz3.dll" pe-x64
stage_native win-x64 "$WIN_TMP"/*

extract_one "$DOWNLOADS/z3-osx-x64.zip" "z3-${Z3_VERSION}-x64-osx-10.16/bin/libz3.dylib" "$CACHE/libz3-osx-x64.dylib"
expect_kind "$CACHE/libz3-osx-x64.dylib" macho-x64
mkdir -p "$STAGED/osx-x64/native"
cp -f "$CACHE/libz3-osx-x64.dylib" "$STAGED/osx-x64/native/libz3.dylib"

extract_one "$DOWNLOADS/z3-osx-arm64.zip" "z3-${Z3_VERSION}-arm64-osx-11.0/bin/libz3.dylib" "$CACHE/libz3-osx-arm64.dylib"
expect_kind "$CACHE/libz3-osx-arm64.dylib" macho-arm64
mkdir -p "$STAGED/osx-arm64/native"
cp -f "$CACHE/libz3-osx-arm64.dylib" "$STAGED/osx-arm64/native/libz3.dylib"

jobs() {
  if command -v nproc >/dev/null 2>&1; then nproc
  else echo 4
  fi
}

build_linux_arm64() {
  local compat="$ROOT/build/z3/glibc-compat.h"
  local stamp="z3-4.12.2 single-threaded static-libstdc++ $(sha256_file "$compat")"
  local out="$CACHE/linux-arm64"
  if [[ -f "$out/libz3.so" && -f "$out/BUILDINFO" && "$(cat "$out/BUILDINFO")" == "$stamp" ]]; then
    echo "cached linux-arm64 libz3.so"
    stage_native linux-arm64 "$out/libz3.so"
    return
  fi
  if ! command -v aarch64-linux-gnu-g++ >/dev/null 2>&1; then
    echo "aarch64-linux-gnu-g++ is required to build linux-arm64 libz3 (apt install g++-aarch64-linux-gnu)" >&2
    exit 1
  fi
  if ! command -v patchelf >/dev/null 2>&1; then
    echo "patchelf is required to set the linux-arm64 libz3 soname" >&2
    exit 1
  fi
  if [[ ! -d "$CACHE/src/.git" ]]; then
    git clone --depth 1 --branch "$Z3_TAG" https://github.com/Z3Prover/z3.git "$CACHE/src"
  fi
  local build="$CACHE/linux-arm64-build"
  rm -rf "$build"
  cmake -S "$CACHE/src" -B "$build" \
    -DCMAKE_POLICY_VERSION_MINIMUM=3.5 \
    -DCMAKE_BUILD_TYPE=Release \
    -DCMAKE_SYSTEM_NAME=Linux \
    -DCMAKE_SYSTEM_PROCESSOR=aarch64 \
    -DCMAKE_C_COMPILER=aarch64-linux-gnu-gcc \
    -DCMAKE_CXX_COMPILER=aarch64-linux-gnu-g++ \
    -DCMAKE_C_FLAGS="-include $compat" \
    -DCMAKE_CXX_FLAGS="-include cstdint -include $compat" \
    -DZ3_BUILD_LIBZ3_SHARED=ON \
    -DZ3_SINGLE_THREADED=ON \
    -DZ3_USE_LIB_GMP=OFF \
    -DZ3_ENABLE_EXAMPLE_TARGETS=OFF \
    -DZ3_BUILD_DOCUMENTATION=OFF \
    -DZ3_INCLUDE_GIT_HASH=OFF \
    -DZ3_INCLUDE_GIT_DESCRIBE=OFF \
    -DCMAKE_SHARED_LINKER_FLAGS="-static-libstdc++ -static-libgcc"
  cmake --build "$build" -j"$(jobs)" --target libz3
  mkdir -p "$out"
  cp -L "$build/libz3.so" "$out/libz3.so"
  patchelf --set-soname libz3.so "$out/libz3.so"
  expect_kind "$out/libz3.so" elf-arm64
  local max
  max=$(aarch64-linux-gnu-objdump -T "$out/libz3.so" | grep -oE 'GLIBC_[0-9.]+' | sort -t_ -k2 -V | tail -1 || true)
  echo "$stamp" > "$out/BUILDINFO"
  echo "${max:-unknown}" > "$out/GLIBC"
  echo "linux-arm64 libz3 needs ${max:-unknown}"
  rm -rf "$build"
  stage_native linux-arm64 "$out/libz3.so"
}

if [[ "$BUILD_LINUX_ARM64" == 1 ]]; then build_linux_arm64; fi

# A linux-arm64 library built on an earlier run is still packed when this run did not rebuild it.
if [[ -d "$CACHE/linux-arm64" && ! -d "$STAGED/linux-arm64/native" && -f "$CACHE/linux-arm64/libz3.so" ]]; then
  stage_native linux-arm64 "$CACHE/linux-arm64/libz3.so"
fi

"$PY" - "$ROOT" "$MANAGED" "$STAGED" "$NUPKG_DIR" <<'PY'
import pathlib, sys, zipfile, textwrap
root, managed, staged, feed = map(pathlib.Path, sys.argv[1:5])
nuspec = (root / "build/z3/VSharp.Z3.nuspec").read_bytes()
pkg = root / "build/.cache/z3/vsharp.z3.4.12.2.nupkg"
files = []
files.append(("lib/netstandard2.0/Microsoft.Z3.dll", managed / "Microsoft.Z3.dll"))
xml = managed / "Microsoft.Z3.xml"
if xml.exists():
    files.append(("lib/netstandard2.0/Microsoft.Z3.xml", xml))
files.append(("LICENSE-Z3.txt", root / "build/.cache/z3/LICENSE-Z3.txt"))
for native in sorted(staged.glob("*/*/*")):
    if native.is_file() and native.name != "BUILDINFO" and native.name != "GLIBC":
        rel = native.relative_to(staged).as_posix()
        files.append((f"runtimes/{rel}", native))
rels = textwrap.dedent("""\
    <?xml version="1.0" encoding="utf-8"?>
    <Relationships xmlns="http://schemas.openxmlformats.org/package/2006/relationships">
      <Relationship Type="http://schemas.openxmlformats.org/package/2006/relationships/metadata/core-properties" Target="/VSharp.Z3.nuspec" Id="nuspec" />
    </Relationships>
    """).encode()
ctypes = textwrap.dedent("""\
    <?xml version="1.0" encoding="utf-8"?>
    <Types xmlns="http://schemas.openxmlformats.org/package/2006/content-types">
      <Default Extension="rels" ContentType="application/vnd.openxmlformats-package.relationships+xml" />
      <Default Extension="nuspec" ContentType="application/octet-stream" />
      <Default Extension="dll" ContentType="application/octet-stream" />
      <Default Extension="so" ContentType="application/octet-stream" />
      <Default Extension="dylib" ContentType="application/octet-stream" />
      <Default Extension="xml" ContentType="application/octet-stream" />
      <Default Extension="txt" ContentType="application/octet-stream" />
    </Types>
    """).encode()
pkg.parent.mkdir(parents=True, exist_ok=True)
with zipfile.ZipFile(pkg, "w", compression=zipfile.ZIP_DEFLATED) as z:
    z.writestr("VSharp.Z3.nuspec", nuspec)
    z.writestr("_rels/.rels", rels)
    z.writestr("[Content_Types].xml", ctypes)
    for arc, path in files:
        z.write(path, arc)
print(f"packed {pkg} ({len(files)} files)")
PY

rm -rf "$NUPKG_DIR"
mkdir -p "$NUPKG_DIR"
# A folder feed is the nupkg sitting in the directory. Hierarchical push is unnecessary
# and rejects a hand-built package that has no source URL.
cp -f "$CACHE/vsharp.z3.4.12.2.nupkg" "$NUPKG_DIR/vsharp.z3.4.12.2.nupkg"
rm -rf "${NUGET_PACKAGES:-$HOME/.nuget/packages}/vsharp.z3"
echo "VSharp.Z3 4.12.2 is in $NUPKG_DIR"
