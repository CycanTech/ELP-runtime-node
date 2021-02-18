# Everlasting Network Parachain
  Everlasting Network Paranchain base in rococo-v1, buildin contracts supports. 
This contracts interface supports Substrate 2.0+ with contracts using Ink! 3.0+ & EVM.

## Build & Run

### Launch the Rococo RelayChain

```bash
# Compile Polkadot with the real overseer feature
git clone -b rococo-v1 https://github.com/paritytech/polkadot
cargo build --release --features=real-overseer

# Generate a raw chain spec
./target/release/polkadot \
  build-spec \
  --chain rococo-local \
  --disable-default-bootnode \ 
  --raw \
  > rococo-local-raw.json

# Alice
./target/release/polkadot \
  --chain rococo-local-raw.json \
  --alice \
  --tmp \
  > relayA.out 2>&1 &

# Bob
./target/release/polkadot \
  --chain rococo-local-raw.json \
  --bob \
  --tmp \
  --port 30334 \
  > relayB.out 2>&1 &
```

### Launch the EverLasting Parachain

```bash
# Compile
git clone https://github.com/szout/everlasting-network
cargo build --release

# Export genesis state
./target/release/everlasting-collator \
  export-genesis-state \
  --parachain-id 200 \
  > genesis-state

# Export genesis wasm
./target/release/everlasting-collator \
  export-genesis-wasm \
  > genesis-wasm

# Collator1
./target/release/everlasting-collator \
  --collator \
  --tmp \
  --parachain-id 200 \
  --port 40335 \
  --ws-port 9946 \
  -- \
  --execution wasm \
  --chain ../polkadot/rococo-local-raw.json \
  --port 30335 \
  > Collator1.out 2>&1 &

# Collator2
./target/release/everlasting-collator \ 
  --collator \  
  --tmp \ 
  --parachain-id 200 \ 
  --port 40336 \ 
  --ws-port 9947 \ 
  -- \ 
  --execution wasm \ 
  --chain ../polkadot/rococo-local-raw.json \ 
  --port 30336 \ 
  > Collator2.out 2>&1 &

# Parachain Full Node
./target/release/everlasting-collator \
  --tmp \
  --parachain-id 200 \
  --port 40337 \
  --ws-port 9948 \
  -- \
  --execution wasm \
  --chain ../polkadot/rococo-local-raw.json \
  --port 30337 \
  > FullNode.out 2>&1 &
```
### Register the everlasting parachain
```bash
# polkadot.js ui 
https://polkadot.js.org/apps/?rpc=ws://127.0.0.1:9944

ui menu level
sudo
  parasSudoWrapper
    sudoScheduleParaInitialize(id, genesis)

input items:
            id <- 200
   genesisHead <- genesis-state(above)
validationCode <- genesis-wasm (above)
     parachain <- true
```
