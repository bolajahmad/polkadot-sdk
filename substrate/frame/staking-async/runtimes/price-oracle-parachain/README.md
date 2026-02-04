# Price Oracle Parachain

#### What

First, what is this folder? This is `staking-async/runtimes`, a clone of westend/asset-hub-westend that we have heavily
altered to test staking in AHM. For simplicity, I have put my prototype here.

I have a helper script that runs everything. All you need to do is to make sure `zombienet` is in your path. Then:

1. go to `cd substrate/frame/staking-async/runtimes/papi-tests`
2. `just setup`
3. `bun run src/index.ts price-oracle`

Make sure you have the latest version zombienet, as it contains some fixes that are needed to work here.


#### Organization

Final zombienet config is: `zn-oracle.toml`. It runs:

1. `pallet-staking-async-rc-runtime`
2. `pallet-staking-async-price-oracle-parachain-runtime`
3. (and the WAH clone, called `pallet-staking-async-parachain-runtime`)

The new pallets are in the `price-oracle-parachain-runtime`. They are:

1. `price_oracle`: Where we run the offchain worker
2. `rc_client`: The one receiving validators from the RC, and acting as the local session manager of the price-oracle
   parachain.

#### How it works

We use pretty much only existing traits and mechanisms to forward new validator sets to the price-oracle and integrate
them in an existing session pallet, with a bit of gymnastics. It is explained in `price-oracle/src/lib.rs` docs.
