spec aptos_framework::state_storage {
    spec module {
        use aptos_std::chain_status;
        pragma verify = true;
        pragma aborts_if_is_strict;
        // property 1: After genesis, `StateStorageUsage` and `GasParameter` exist.
        // property 5: The StateStorageUsage structure exists before performing any further operations.
        invariant [suspendable] chain_status::is_operating() ==> exists<StateStorageUsage>(@aptos_framework);
        invariant [suspendable] chain_status::is_operating() ==> exists<GasParameter>(@aptos_framework);
    }

    /// ensure caller is admin.
    /// aborts if StateStorageUsage already exists.
    spec initialize(aptos_framework: &signer) {
        use std::signer;
        let addr = signer::address_of(aptos_framework);
        // property 4: Only the admin address maycall the initialization function.
        aborts_if !system_addresses::is_aptos_framework_address(addr);
        // property 3: The initialization function is only called once, during genesis.
        aborts_if exists<StateStorageUsage>(@aptos_framework);

        // property 2: The resource for tracking state storage usage may only be initialized with specific values and published under the aptos_framework account.
        ensures exists<StateStorageUsage>(@aptos_framework);
        let post state_usage = global<StateStorageUsage>(@aptos_framework);
        ensures state_usage.epoch == 0 && state_usage.usage.bytes == 0 && state_usage.usage.items == 0;
    }

    spec on_new_block(epoch: u64) {
        use aptos_std::chain_status;
        // property 5: The StateStorageUsage structure exists before performing any further operations.
        requires chain_status::is_operating();

        aborts_if false;
        ensures epoch == global<StateStorageUsage>(@aptos_framework).epoch;
    }

    spec current_items_and_bytes(): (u64, u64) {
        // property 5: The StateStorageUsage structure exists before performing any further operations.
        aborts_if !exists<StateStorageUsage>(@aptos_framework);

        let usage = global<StateStorageUsage>(@aptos_framework).usage;
        ensures result_1 == usage.items;
        ensures result_2 == usage.bytes;
    }

    spec get_state_storage_usage_only_at_epoch_beginning(): Usage {
        // TODO: temporary mockup.
        pragma opaque;
    }

    spec on_reconfig {
        aborts_if true;
    }
}
