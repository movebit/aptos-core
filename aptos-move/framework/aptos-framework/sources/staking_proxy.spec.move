spec aptos_framework::staking_proxy {
    spec module {
        pragma verify = true;
        pragma aborts_if_is_strict;
    }

    /// Aborts if conditions of SetStakePoolOperator are not met
    spec set_operator(owner: &signer, old_operator: address, new_operator: address) {
        // TODO: Can't verify `set_vesting_contract_operator` and `set_staking_contract_operator`
        pragma aborts_if_is_partial;
        include SetStakingContractOperatorAbortsIf;
        include SetStakePoolOperator;
    }

    /// Aborts if conditions of SetStackingContractVoter and SetStackPoolVoterAbortsIf are not met
    spec set_voter(owner: &signer, operator: address, new_voter: address) {
        // TODO: Can't verify `set_vesting_contract_voter`
        pragma aborts_if_is_partial;
        include SetStakingContractVoter;
        include SetStakePoolVoterAbortsIf;
    }

    spec set_vesting_contract_operator(owner: &signer, old_operator: address, new_operator: address) {
        // TODO: Can't verify `update_voter` in while loop.
        pragma aborts_if_is_partial;
    }

    spec set_staking_contract_operator(owner: &signer, old_operator: address, new_operator: address) {
        use aptos_std::simple_map;
        use aptos_framework::staking_contract::{Store};
        // TODO: Verify timeout and can't verify `staking_contract::switch_operator`.
        pragma verify = true;
        pragma aborts_if_is_partial;

        include SetStakingContractOperatorAbortsIf;
    }

    spec schema SetStakingContractOperatorAbortsIf {
        use aptos_framework::staking_contract::{Store};
        use aptos_framework::simple_map;
        use aptos_framework::timestamp;

        owner: signer;
        old_operator: address;
        new_operator: address;

        let owner_address = signer::address_of(owner);
        let store = global<Store>(owner_address);
        let staking_contract_exists = exists<Store>(owner_address) && simple_map::spec_contains_key(store.staking_contracts, old_operator);
        let staking_contracts = global<Store>(owner_address).staking_contracts;
        let post post_staking_contracts = global<Store>(owner_address).staking_contracts;
        let current_commission_percentage = simple_map::spec_get(staking_contracts, old_operator).commission_percentage;
        aborts_if staking_contract_exists && simple_map::spec_contains_key(staking_contracts, new_operator);
        let staking_contract = simple_map::spec_get(staking_contracts, old_operator);
        ensures staking_contract_exists ==> !simple_map::spec_contains_key(post_staking_contracts, old_operator);

        let pool_address = staking_contract.pool_address;
        aborts_if staking_contract_exists && !exists<stake::StakePool>(pool_address);
        let stake_pool = global<stake::StakePool>(pool_address);
        let inactive = stake_pool.inactive.value;
        let pending_inactive = stake_pool.pending_inactive.value;
        aborts_if staking_contract_exists && inactive + pending_inactive > MAX_U64;

        // verify stake::withdraw_with_cap()
        let total_potential_withdrawable = inactive + pending_inactive;
        let pool_address_1 = staking_contract.owner_cap.pool_address;
        aborts_if staking_contract_exists && !exists<stake::StakePool>(pool_address_1);
        let stake_pool_1 = global<stake::StakePool>(pool_address_1);
        aborts_if staking_contract_exists && !exists<stake::ValidatorSet>(@aptos_framework);
        let validator_set = global<stake::ValidatorSet>(@aptos_framework);
        let inactive_state = !stake::spec_contains(validator_set.pending_active, pool_address_1)
            && !stake::spec_contains(validator_set.active_validators, pool_address_1)
            && !stake::spec_contains(validator_set.pending_inactive, pool_address_1);
        let inactive_1 = stake_pool_1.inactive.value;
        let pending_inactive_1 = stake_pool_1.pending_inactive.value;
        let new_inactive_1 = inactive_1 + pending_inactive_1;
        aborts_if staking_contract_exists && inactive_state && timestamp::spec_now_seconds() >= stake_pool_1.locked_until_secs
            && inactive_1 + pending_inactive_1 > MAX_U64;
    }

    spec set_vesting_contract_voter(owner: &signer, operator: address, new_voter: address) {
        // TODO: Can't verify `update_voter` in while loop.
        pragma aborts_if_is_partial;
    }

    /// Aborts if stake_pool is exists and when OwnerCapability or stake_pool_exists
    /// One of them are not exists
    spec set_stake_pool_operator(owner: &signer, new_operator: address) {
        include SetStakePoolOperator;
    }

    spec schema SetStakePoolOperator {
        owner: &signer;
        new_operator: address;

        let owner_address = signer::address_of(owner);
        let ownership_cap = borrow_global<stake::OwnerCapability>(owner_address);
        let pool_address = ownership_cap.pool_address;
        aborts_if stake::stake_pool_exists(owner_address) && !(exists<stake::OwnerCapability>(owner_address) && stake::stake_pool_exists(pool_address));
    }

    spec set_staking_contract_voter(owner: &signer, operator: address, new_voter: address) {
        include SetStakingContractVoter;
    }

    /// Make sure staking_contract_exists first
    /// Then abort if the resource is not exist
    spec schema SetStakingContractVoter {
        use aptos_std::simple_map;
        use aptos_framework::staking_contract::{Store};

        owner: &signer;
        operator: address;
        new_voter: address;


        let owner_address = signer::address_of(owner);
        let staker = owner_address;
        let store = global<Store>(staker);

        // in staking_contract_exists
        let staking_contract_exists = exists<Store>(staker) && simple_map::spec_contains_key(store.staking_contracts, operator);

        // in update_voter
        let staker_address = owner_address;
        let staking_contract = simple_map::spec_get(store.staking_contracts, operator);
        let pool_address = staking_contract.pool_address;

        aborts_if staking_contract_exists && !exists<stake::StakePool>(pool_address);
        aborts_if staking_contract_exists && !exists<stake::StakePool>(staking_contract.owner_cap.pool_address);

    }

    spec set_stake_pool_voter(owner: &signer, new_voter: address) {
        include SetStakePoolVoterAbortsIf;
    }

    spec schema SetStakePoolVoterAbortsIf {
        owner: &signer;
        new_voter: address;

        let owner_address = signer::address_of(owner);
        let ownership_cap = global<stake::OwnerCapability>(owner_address);
        let pool_address = ownership_cap.pool_address;
        aborts_if stake::stake_pool_exists(owner_address) && !(exists<stake::OwnerCapability>(owner_address) && stake::stake_pool_exists(pool_address));
    }
}
