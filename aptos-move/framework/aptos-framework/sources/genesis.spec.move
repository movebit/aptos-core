spec aptos_framework::genesis {
    spec module {
        // We are not proving each genesis step individually. Instead, we construct
        // and prove `initialize_for_verification` which is a "#[verify_only]" function that
        // simulates the genesis encoding process in `vm-genesis` (written in Rust).
        // So, we turn off the verification at the module level, but turn it on for
        // the verification-only function `initialize_for_verification`.
        pragma verify = false;
    }

    spec initialize_for_verification {
        use aptos_framework::account::Account;
        pragma verify = true;

        // property 1: All system resources and modules should be created during genesis and owned or deployed by the Aptos framework account.
        ensures exists<aptos_governance::GovernanceResponsbility>(@aptos_framework)
            && exists<consensus_config::ConsensusConfig>(@aptos_framework)
            && exists<execution_config::ExecutionConfig>(@aptos_framework)
            && exists<version::Version>(@aptos_framework)
            && exists<version::SetVersionCapability>(@aptos_framework)
            && exists<stake::ValidatorSet>(@aptos_framework)
            && exists<stake::ValidatorPerformance>(@aptos_framework)
            && exists<staking_config::StakingConfig>(@aptos_framework)
            && exists<storage_gas::StorageGasConfig>(@aptos_framework)
            && exists<storage_gas::StorageGas>(@aptos_framework)
            && exists<gas_schedule::GasScheduleV2>(@aptos_framework)
            && exists<aggregator_factory::AggregatorFactory>(@aptos_framework)
            && exists<coin::SupplyConfig>(@aptos_framework)
            && exists<chain_id::ChainId>(@aptos_framework)
            && exists<reconfiguration::Configuration>(@aptos_framework)
            && exists<block::BlockResource>(@aptos_framework)
            && exists<state_storage::StateStorageUsage>(@aptos_framework)
            && exists<timestamp::CurrentTimeMicroseconds>(@aptos_framework);

        // property 2: Addresses ranging from 0x0 - 0xa should be reserved for the framework and part of aptos governance.
        ensures exists<Account>(@0x1)
            && exists<Account>(@0x2)
            && exists<Account>(@0x3)
            && exists<Account>(@0x4)
            && exists<Account>(@0x5)
            && exists<Account>(@0x6)
            && exists<Account>(@0x7)
            && exists<Account>(@0x8)
            && exists<Account>(@0x9)
            && exists<Account>(@0xa);

        // property 4: An initial set of validators should exist before the end of genesis.
        let validator_set = global<stake::ValidatorSet>(@aptos_framework);
        let total = len(validator_set.active_validators);
        ensures total >= 1;
    }
}
