# Template. build/package.sh writes artifacts/homebrew/vsharpc.rb with real checksums.
# The maintainer copies that file into a tap (a separate repository, for example
# github.com/bluechiperic/homebrew-vsharp) and users run `brew tap` / `brew install vsharpc`.
# This repository does not publish the tap. Formulae install the release tarball;
# codesign and notarization of that tarball are still the maintainer's step.
class Vsharpc < Formula
  desc "V# compiler: prove function contracts and emit .NET IL"
  homepage "https://github.com/bluechiperic/vsharp"
  version "0.1.0"
  license "Apache-2.0"

  on_macos do
    on_arm do
      url "https://github.com/bluechiperic/vsharp/releases/download/v0.1.0/vsharpc-0.1.0-osx-arm64.tar.gz"
      sha256 "REPLACE_WITH_SHA256"
    end
    on_intel do
      url "https://github.com/bluechiperic/vsharp/releases/download/v0.1.0/vsharpc-0.1.0-osx-x64.tar.gz"
      sha256 "REPLACE_WITH_SHA256"
    end
  end

  on_linux do
    on_arm do
      url "https://github.com/bluechiperic/vsharp/releases/download/v0.1.0/vsharpc-0.1.0-linux-arm64.tar.gz"
      sha256 "REPLACE_WITH_SHA256"
    end
    on_intel do
      url "https://github.com/bluechiperic/vsharp/releases/download/v0.1.0/vsharpc-0.1.0-linux-x64.tar.gz"
      sha256 "REPLACE_WITH_SHA256"
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
