/usr/bin/ruby -e "$(curl -fsSL https://raw.githubusercontent.com/Homebrew/install/master/install)"
brew install openssl cmake
curl https://sh.rustup.rs -sSf | sh
source ~/.cargo/env
cargo install --git https://github.com/paritytech/substrate subkey
cargo install --git https://github.com/paritytech/substrate substrate
