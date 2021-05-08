# Phoenix Parachain
  Phoenix Paranchain base in rococo-v1, buildin contracts supports. 
This contracts interface supports Substrate 3.0 with contracts using Ink! 3.0.
 suport EVM & Ethereum API
```bash
include pallets list:
   pallet_timestamp
   pallet_balances
   pallet_sudo
   pallet_randomness_collective_flip
   cumulus_parachain_system
   pallet_transaction_payment
   parachain_info
   xcm_handler
   pallet_evm
   pallet_ethereum
   pallet_contracts
   pallet_scheduler
   pallet_democracy
   pallet_elections_phragmen 
   offchain_worker
   price_fetch
```

## Build & Run

### Launch the Rococo RelayChain

```bash
# Compile Polkadot v30 fork
git clone https://github.com/CycanTech/polkadot.git 
cargo build --release 

# Generate a raw chain spec
./target/release/polkadot \
  build-spec \
  --chain rococo-local \
  --disable-default-bootnode \ 
  --raw \
  > rococo-local-raw.json

# Alice
./target/release/polkadot \
  --base-path ../data/rococo-relay1 \
  --chain rococo-local-raw.json \
  --rpc-methods Unsafe \
  --ws-port 9944 \
  --validator \
  --alice \
  --port 50556 \
  --ws-external \
  --rpc-external \
  --rpc-cors all \
>../log/relayA.out 2>&1 &

sleep 1

# Bob
./target/release/polkadot \
  --base-path ../data/rococo-relay2 \
  --chain rococo-local-raw.json \
  --ws-port 9943 \
  --validator \
   --bob \
  --port 50555 \
>../log/relayB.out 2>&1 &

```

### Launch the Phoenix Parachain

```bash
# Compile
git clone https://github.com/CycanTech/ELP-runtime-node
cargo build --release

# make work dir
mkdir ../data
mkdir ../log

# Export genesis state
./target/release/phoenix-collator \
  export-genesis-state \
  --parachain-id 6806 \
  > genesis-state

# Export genesis wasm
./target/release/phoenix-collator \
  export-genesis-wasm \
  > genesis-wasm

# Export spec file
./target/release/phoenix-collator \
  build-spec  \
  --disable-default-bootnode \
  > phoenix-src.json

./target/release/phoenix-collator \
  build-spec \
  --chain phoenix-src.json \
  --disable-default-bootnode \
  --raw \
  > phoenix-raw.json

# Collator1
./target/release/phoenix-collator \
  --collator \
  --base-path ../data/phoenix-c1 \
  --parachain-id 6806 \
  --chain phoenix-raw.json \
  --rpc-methods Unsafe \
  --ws-external \
  --rpc-external \
  --rpc-cors all \
  --ws-port 9966 \
  --rpc-port 9955 \
  --port 40335 \
  -- \
  --execution wasm \
  --chain rococo-local-raw.json \
  --port 30335
> ../log/Collator1.out 2>&1 &

```
### Register the phoenix parachain
```bash
# polkadot.js UI 
https://polkadot.js.org/apps/?rpc=ws://127.0.0.1:9944

UI menu level
sudo
  parasSudoWrapper
    sudoScheduleParaInitialize(id, genesis)

input items:
            id <- 6806 
   genesisHead <- genesis-state(above)
validationCode <- genesis-wasm (above)
     parachain <- true
```
