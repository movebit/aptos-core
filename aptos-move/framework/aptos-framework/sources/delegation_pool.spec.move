spec aptos_framework::delegation_pool {
    spec module {
        // TODO: verification disabled until this module is specified.
        pragma verify = false;
        pragma aborts_if_is_strict;
    }

    spec owner_cap_exists(addr: address): bool {
        pragma verify = true;
        aborts_if false;
    }

    spec get_owned_pool_address(owner: address): address {
        pragma verify = true;
        aborts_if !exists<DelegationPoolOwnership>(owner);
    }

    /// Return whether a delegation pool exists at supplied address `addr`.
    spec delegation_pool_exists(addr: address): bool {
        pragma verify = true;
        aborts_if false;
    }

    spec observed_lockup_cycle(pool_address: address): u64 {
        pragma verify = true;
        aborts_if !exists<DelegationPool>(pool_address);
    }

    spec operator_commission_percentage(pool_address: address): u64 {
        pragma verify = true;
        aborts_if !exists<DelegationPool>(pool_address);
    }

    spec shareholders_count_active_pool(pool_address: address): u64 {
        pragma verify = true;
        aborts_if !exists<DelegationPool>(pool_address);
    }

    spec get_delegation_pool_stake(pool_address: address): (u64, u64, u64, u64) {
        pragma verify = true;
        aborts_if !exists<DelegationPool>(pool_address);
        aborts_if !stake::stake_pool_exists(pool_address);
    }

    spec get_pending_withdrawal(
        pool_address: address,
        delegator_address: address
    ): (bool, u64) {
        pragma verify = false;
        aborts_if !delegation_pool_exists(pool_address);
        // aborts_if !exists<DelegationPool>(pool_address);
        // aborts_if !stake::stake_pool_exists(pool_address);
    }

    spec get_stake(pool_address: address, delegator_address: address): (u64, u64, u64) {

    }

    spec get_add_stake_fee(pool_address: address, amount: u64): u64 {

    }

    spec can_withdraw_pending_inactive(pool_address: address): bool {
        pragma verify = false;
        // aborts_if !exists<stake::ValidatorSet>(@aptos_framework);
    }

    spec initialize_delegation_pool(
        owner: &signer,
        operator_commission_percentage: u64,
        delegation_pool_creation_seed: vector<u8>,
    ) {
        pragma verify = false;
    }

    spec assert_owner_cap_exists(owner: address) {
        pragma verify = true;
        aborts_if !owner_cap_exists(owner);
    }

    spec assert_delegation_pool_exists(pool_address: address) {
        pragma verify = true;
        aborts_if !delegation_pool_exists(pool_address);
    }

    spec assert_min_active_balance(pool: &DelegationPool, delegator_address: address) {
        pragma verify = true;
        let pool_u64 = pool.active_shares;
        include AssertMinActiveBalanceAbortsIf;
    }
    spec schema AssertMinActiveBalanceAbortsIf {
        pool_u64: pool_u64::Pool;
        delegator_address: address;
        let shares = pool_u64::spec_shares(pool_u64, delegator_address);
        let total_coins = pool_u64.total_coins;
        let balance = pool_u64::spec_shares_to_amount_with_total_coins(pool_u64, shares, total_coins);
        aborts_if pool_u64.total_coins > 0 && pool_u64.total_shares > 0 && (shares * total_coins) / pool_u64.total_shares > MAX_U64;
        aborts_if balance < MIN_COINS_ON_SHARES_POOL;
    }

    spec assert_min_pending_inactive_balance(pool: &DelegationPool, delegator_address: address) {
        pragma verify = true;
        let observed_lockup_cycle = pool.observed_lockup_cycle;
        aborts_if !table::spec_contains(pool.inactive_shares, observed_lockup_cycle);
        let pool_u64 = table::spec_get(pool.inactive_shares, observed_lockup_cycle);
        include AssertMinActiveBalanceAbortsIf;
    }

    spec coins_to_redeem_to_ensure_min_stake(
        src_shares_pool: &pool_u64::Pool,
        shareholder: address,
        amount: u64,
    ): u64 {
        pragma verify = true;
        include AmountToSharesToRedeemAbortsIf {
            shares_pool: src_shares_pool,
        };
    }

    spec coins_to_transfer_to_ensure_min_stake(
        src_shares_pool: &pool_u64::Pool,
        dst_shares_pool: &pool_u64::Pool,
        shareholder: address,
        amount: u64,
    ): u64 {
        pragma verify = false;
        include AmountToSharesToRedeemAbortsIf {
            shares_pool: src_shares_pool,
        };
        // let shares_to_redeem = spec_amount_to_shares_to_redeem(src_shares_pool, shareholder, amount);
        //  aborts_if src_shares_pool.total_coins > 0 && src_shares_pool.total_shares > 0
        //     && (shares_to_redeem * src_shares_pool.total_coins) / src_shares_pool.total_shares > MAX_U64;
        // include AmountToSharesToRedeemAbortsIf {
        //     shares_pool: src_shares_pool,
        //     shareholder: shares_to_redeem,
        // };
    }

    spec retrieve_stake_pool_owner(pool: &DelegationPool): signer {
        pragma verify = true;
        aborts_if false;
    }

    spec get_pool_address(pool: &DelegationPool): address {
        pragma verify = true;
        aborts_if false;
    }

    spec olc_with_index(index: u64): ObservedLockupCycle {
        pragma verify = true;
        aborts_if false;
    }

    spec set_operator(
        owner: &signer,
        new_operator: address
    ) {

    }

    spec set_delegated_voter(
        owner: &signer,
        new_voter: address
    ) {

    }

    spec add_stake(delegator: &signer, pool_address: address, amount: u64) {

    }

    spec unlock(delegator: &signer, pool_address: address, amount: u64) {

    }

    spec reactivate_stake(delegator: &signer, pool_address: address, amount: u64) {

    }

    spec withdraw(delegator: &signer, pool_address: address, amount: u64) {

    }

    spec withdraw_internal(pool: &mut DelegationPool, delegator_address: address, amount: u64) {

    }

    spec pending_withdrawal_exists(pool: &DelegationPool, delegator_address: address): (bool, ObservedLockupCycle) {

    }

    spec pending_inactive_shares_pool_mut(pool: &mut DelegationPool): &mut pool_u64::Pool {
        pragma verify = true;
        let observed_lockup_cycle = pool.observed_lockup_cycle;
        aborts_if !table::spec_contains(pool.inactive_shares, observed_lockup_cycle);
    }

    spec pending_inactive_shares_pool(pool: &DelegationPool): &pool_u64::Pool {

    }

    spec execute_pending_withdrawal(pool: &mut DelegationPool, delegator_address: address) {

    }

    spec buy_in_pending_inactive_shares(
        pool: &mut DelegationPool,
        shareholder: address,
        coins_amount: u64,
    ): u128 {
        pragma verify = false;
        let observed_lockup_cycle = pool.observed_lockup_cycle;
        aborts_if !table::spec_contains(pool.inactive_shares, observed_lockup_cycle);
    }

    spec amount_to_shares_to_redeem(
        shares_pool: &pool_u64::Pool,
        shareholder: address,
        coins_amount: u64,
    ): u128 {
        pragma verify = true;
        include AmountToSharesToRedeemAbortsIf;
        ensures result == spec_amount_to_shares_to_redeem(shares_pool, shareholder, coins_amount);
    }
    spec schema AmountToSharesToRedeemAbortsIf {
        shares_pool: pool_u64::Pool;
        shareholder: address;
        let shares = pool_u64::spec_shares(shares_pool, shareholder);
        let total_coins = shares_pool.total_coins;
        aborts_if shares_pool.total_coins > 0 && shares_pool.total_shares > 0 && (shares * total_coins) / shares_pool.total_shares > MAX_U64;
    }

    spec fun spec_amount_to_shares_to_redeem(
        shares_pool: pool_u64::Pool,
        shareholder: address,
        coins_amount: u64,
    ): u128 {
        let shares = pool_u64::spec_shares(shares_pool, shareholder);
        let total_coins = shares_pool.total_coins;
        let balance = pool_u64::spec_shares_to_amount_with_total_coins(shares_pool, shares, total_coins);
        if (coins_amount >= balance) {
            shares
        } else {
            pool_u64::spec_amount_to_shares_with_total_coins(shares_pool, coins_amount, total_coins)
        }
    }

    spec redeem_active_shares(
        pool: &mut DelegationPool,
        shareholder: address,
        coins_amount: u64,
    ): u64 {
        pragma verify = true;

        let shares_pool = pool.active_shares;

        include AmountToSharesToRedeemAbortsIf;

        let shares_to_redeem = spec_amount_to_shares_to_redeem(pool.active_shares, shareholder, coins_amount);
        let redeemed_coins = pool_u64::spec_shares_to_amount_with_total_coins(shares_pool, shares_to_redeem, shares_pool.total_coins);

        aborts_if pool_u64::spec_shares(shares_pool, shareholder) < shares_to_redeem;
        aborts_if shares_pool.total_coins < redeemed_coins;
        aborts_if shares_pool.total_shares < shares_to_redeem;
    }

    spec redeem_inactive_shares(
        pool: &mut DelegationPool,
        shareholder: address,
        coins_amount: u64,
        lockup_cycle: ObservedLockupCycle,
    ): u64 {
        pragma verify = false;
        // let observed_lockup_cycle = pool.observed_lockup_cycle;
        // aborts_if !table::spec_contains(pool.inactive_shares, lockup_cycle);

    }

    spec calculate_stake_pool_drift(pool: &DelegationPool): (bool, u64, u64, u64, u64) {
        pragma verify = false;
    }

    spec synchronize_delegation_pool(pool_address: address) {

    }

    spec multiply_then_divide(x: u64, y: u64, z: u64): u64 {
        pragma verify = true;
        aborts_if (x * y) / z > MAX_U64;
        aborts_if z == 0;
        ensures result == x * y / z;
        ensures z != 0;
    }

    spec to_u128(num: u64): u128 {
        pragma verify = true;
        aborts_if false;
    }
}
