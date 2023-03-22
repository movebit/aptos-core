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
        pragma aborts_if_is_partial = true;
        include stake::ResourceRequirement;
        //requires signer::address_of(owner) != NULL_SHAREHOLDER;
        //Request 1: asserts_if 
        //ERROR
        //Prover can't resolve features::delegation_pools_enabled(), use magic number instead
        aborts_if !features::spec_is_enabled(11);  
        //Request 2: asserts_if exists<DelegationPoolOwnership>(owner) precondition
        //OK
        aborts_if exists<DelegationPoolOwnership>(signer::address_of(owner));
        //Request 3: Sasserts_if operator_commission_percentage > MAX_FEE
        //OK
        aborts_if operator_commission_percentage > MAX_FEE;
        //Request 4: exists<DelegationPoolOwnership>(owner) postcondition
        //OK
        ensures exists<DelegationPoolOwnership>(signer::address_of(owner));
        //Request 5: let pool_address = global<DelegationPoolOwnership>(owner).pool_address;
        //OK
        let post pool_address = global<DelegationPoolOwnership>(signer::address_of(owner)).pool_address;
        //Request 6: exists<DelegationPool>(pool_address)
        //OK
        ensures exists<DelegationPool>(pool_address);
        //Request 7: exists<StakePool>(pool_address)
        //OK
        ensures stake::stake_pool_exists(pool_address);
        //Request 8: table::contains(pool.inactive_shares, pool.OLC): shares pool of pending_inactive stake always exists (cannot be deleted unless it becomes inactive) 
        //OK
        let post pool = global<DelegationPool>(pool_address);
        ensures table::spec_contains(pool.inactive_shares, pool.observed_lockup_cycle); 
        //Request 9: total_coins(pool.active_shares) == active + pending_active on StakePool
        //OK
        let post stake_pool = global<stake::StakePool>(pool_address);
        ensures pool.active_shares.total_coins == coin::value(stake_pool.active) + coin::value(stake_pool.pending_active);
        //Request 10: total_coins(pool.inactive_shares[pool.OLC]) == pending_inactive
        //OK
        ensures table::spec_get(pool.inactive_shares,pool.observed_lockup_cycle).total_coins == coin::value(stake_pool.pending_inactive);
        //Request 11: total_coins_inactive == inactive on StakePool
        //OK
        ensures pool.total_coins_inactive == coin::value(stake_pool.pending_inactive);
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

    

        let pool = global<DelegationPool>(pool_address);
        let source_pool = pool.active_shares;
        let destination_pool = pending_inactive_shares_pool(pool);

        let active =  coin::value(stake_pool.active);
        let inactive =  coin::value(stake_pool.inactive);
        let pending_active = coin::value(stake_pool.pending_active);
        let pending_inactive = coin::value(stake_pool.pending_inactive);

        aborts_if pool_u64::balance(pool.active_shares, delegator) < MIN_COINS_ON_SHARES_POOL;
        ensures active + pending_active == old(active) + old(pending_active) + amount;

        ensures pool.active_shares.total_coins == active + pending_active; 
        ensures pool_u64::shares(pool.active_shares, delegator) - pool_u64::shares(old(pool).active_shares, delegator) == pool_u64::amount_to_shares( old(pool.active_shares), amount - get_add_stake_fee(pool_address, amount));

        ensures pool_u64::shares(pool.active_shares, NULL_SHAREHOLDER) - pool_u64::shares(old(pool).active_shares, NULL_SHAREHOLDER) == pool_u64::amount_to_shares(pool.active_shares, get_add_stake_fee(pool_address, amount));

        ensures pool_u64::balance(pool, delegator) == old(pool_u64::balance(pool, delegator)) - amount;
        
        //resource-account is what?
        ensures pool_u64::balance(pool, retrieve_stake_pool_owner(pool)) == old(pool_u64::balance(pool, retrieve_stake_pool_owner(pool)));

        // aborts_if pool_u64::balance(pool.active_shares, delegator) < MIN_COINS_ON_SHARES_POOL
        // ensures active + pending_active == old(active) + old(pending_active) + amount
        // total_coins(pool.active_shares) == active + pending_active on StakePool
        // pool_u64::shares(pool.active_shares, delegator) - pool_u64::shares(old(pool).active_shares, delegator) ==
        // pool_u64::amount_to_shares(
        // pool.active_shares, // snapshot of shares pool before 1st buy_in
        // amount - get_add_stake_fee(pool_address, amount)
        // )
        // pool_u64::shares(pool.active_shares, NULL_SHAREHOLDER) - pool_u64::shares(old(pool).active_shares, NULL_SHAREHOLDER) == pool_u64::amount_to_shares(
        // pool.active_shares, // snapshot of shares pool before 2nd buy_in
        // get_add_stake_fee(pool_address, amount)
        // )
        // delegator-balance == old(delegator-balance) - amount: delegator sent `amount` APT
        // resource-account-balance == old(resource-account-balance): no stake is lost when transferring through the resource account
        // delegator does not earn rewards from its pending_active stake when this epoch ends


    }

    spec unlock(delegator: &signer, pool_address: address, amount: u64) {
        pragma verify = false;
        // let pool = global<DelegationPool>(pool_address);
        // let source_pool = pool.active_shares;
        // let destination_pool = pending_inactive_shares_pool(pool);

        // let active =  coin::value(stake_pool.active);
        // let inactive =  coin::value(stake_pool.inactive);
        // let pending_active = coin::value(stake_pool.pending_active);
        // let pending_inactive = coin::value(stake_pool.pending_inactive);

        // ensures pool_u64::shares_to_amount( source_pool, pool_u64::shares(old(source_pool), delegator) - pool_u64::shares(source_pool, delegator)) == amount;

        // ensures pool_u64::shares(destination_pool, delegator) - pool_u64::shares(old(destination_pool), delegator) == pool_u64::amount_to_shares(destination_pool, amount);

        // ensures old(source_pool).total_coins - source_pool.total_coins == destination_pool.total_coins - destination_pool.total_coins;        
        // ensures old(source_pool).total_coins - source_pool.total_coins == amount;
        // ensures pool.active_shares - old(pool.active_shares) == old(pending_inactive_shares_pool(pool)) - pending_inactive_shares_pool(pool);

        // ensures pool_u64::balance(pool.inactive_shares[pool.observed_lockup_cycle], delegator) + pool_u64::balance(pool.active_shares, delegator) <= pool_u64::balance(old(inactive_shares[pool.observed_lockup_cycle]), delegator) + pool_u64::balance(old(active_shares), delegator);

        // ensures pending_active == old(pending_active);
        // aborts_if !pool.active_shares.total_coins == active + pending_active;
        // aborts_if !pending_inactive_shares_pool(pool).total_coins == pending_inactive;
        // aborts_if pool_u64::balance(destination_pool, delegator) < MIN_COINS_ON_SHARES_POOL;
        // ensures pool_u64::balance(source_pool, delegator) >= MIN_COINS_ON_SHARES_POOL || 0;
    }

    spec reactivate_stake(delegator: &signer, pool_address: address, amount: u64) {

        // let pool = global<DelegationPool>(pool_address);
        // let source_pool = pool.active_shares;
        // let destination_pool = pending_inactive_shares_pool(pool);

        // let active =  coin::value(stake_pool.active);
        // let inactive =  coin::value(stake_pool.inactive);
        // let pending_active = coin::value(stake_pool.pending_active);
        // let pending_inactive = coin::value(stake_pool.pending_inactive);

        // ensures pool_u64::shares_to_amount( source_pool, pool_u64::shares(old(source_pool), delegator) - pool_u64::shares(source_pool, delegator)) == amount;

        // ensures pool_u64::shares(destination_pool, delegator) - pool_u64::shares(old(destination_pool), delegator) == pool_u64::amount_to_shares(destination_pool, amount);

        // ensures old(source_pool).total_coins - source_pool.total_coins == destination_pool.total_coins - destination_pool.total_coins;        
        // ensures old(source_pool).total_coins - source_pool.total_coins == amount;
        // ensures pool.active_shares - old(pool.active_shares) == old(pending_inactive_shares_pool(pool)) - pending_inactive_shares_pool(pool);

        // ensures pool_u64::balance(pool.inactive_shares[pool.observed_lockup_cycle], delegator) + pool_u64::balance(pool.active_shares, delegator) <= pool_u64::balance(old(inactive_shares[pool.observed_lockup_cycle]), delegator) + pool_u64::balance(old(active_shares), delegator);

        // ensures pending_active == old(pending_active);
        // aborts_if !pool.active_shares.total_coins == active + pending_active;
        // aborts_if !pending_inactive_shares_pool(pool).total_coins == pending_inactive;
        // aborts_if pool_u64::balance(destination_pool, delegator) < MIN_COINS_ON_SHARES_POOL;
        // ensures pool_u64::balance(source_pool, delegator) >= MIN_COINS_ON_SHARES_POOL || 0;
        
        // pool_u64::shares_to_amount(
        // source_pool, // snapshot of shares pool before redeem_shares
        // pool_u64::shares(old(source_pool), delegator) -
        // pool_u64::shares(source_pool, delegator)
        // ) == amount (its latest value)
        // pool_u64::shares(destination_pool, delegator) -
        // pool_u64::shares(old(destination_pool), delegator) ==
        // pool_u64::amount_to_shares(
        // destination_pool, // snapshot of shares pool before buy_in
        // amount (its latest value)
        // )
        // pool_u64::balance(pool.inactive_shares[pool.OLC], delegator) + pool_u64::balance(pool.active_shares, delegator)  <= pool_u64::balance(old(inactive_shares[pool.OLC]), delegator) + pool_u64::balance(old(active_shares), delegator): delegators total internal balance cannot increase
        // total_coins(old(source_pool)) - total_coins(source_pool) ==
        // total_coins(destination_pool) - total_coins(old(destination_pool)) == amount (its latest value)
        // abs(active - old(active)) == abs(pending_inactive - old(pending_inactive))
        // pending_active == old(pending_active): no pending_active stake can be displaced
        // total_coins(pool.active_shares) == active + pending_active on StakePool
        // total_coins(pending_inactive_shares_pool(pool)) == pending_inactive on StakePool
        // aborts_if pool_u64::balance(destination_pool, delegator) < MIN_COINS_ON_SHARES_POOL
        // pool_u64::balance(source_pool, delegator) >= MIN_COINS_ON_SHARES_POOL
        // or == 0
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
        pragma verify = true;
        // let observed_lockup_cycle = pool.observed_lockup_cycle;
        // aborts_if !table::spec_contains(pool.inactive_shares, lockup_cycle);

        // let delegator = get_delegation_pool_stake(pool);
        // let inactiveshares = table::borrow_mut(&mut pool.inactive_shares, lockup_cycle);
        // let shares_to_redeem = amount_to_shares_to_redeem(inactive_shares, shareholder, coins_amount);

        // let active =  coin::value(stake_pool.active);
        // let inactive =  coin::value(stake_pool.inactive);
        // let pending_active = coin::value(stake_pool.pending_active);
        // let pending_inactive = coin::value(stake_pool.pending_inactive);

        // ensures (pool_u64::shares(old(pool.inactive_shares[lockup_cycle]), shareholder) != 0 && pool_u64::shares(pool.inactive_shares[lockup_cycle], shareholder) == 0); 
        // ensures !table::contains(pool.pending_withdrawals, delegator);
        // //how to =>



        // ensures (old(pool.inactive_shares[lockup_cycle].total_coins) - pool_u64::redeem_shares(inactive_shares, shareholder, shares_to_redeem) == 0); 
        // ensures !table::contains(pool.inactive_shares, lockup_cycle);


        // ensures (table::contains(old(pool.pending_withdrawals), delegator) && !table::contains(pool.pending_withdrawals, delegator));
        // ensures old(pool.pending_withdrawals)[delegator] == lockup_cycle;

        // ensures pool_u64::shares(old(pool).inactive_shares[lockup_cycle], shareholder) != 0;
        // ensures pool_u64::shares(pool.inactive_shares[lockup_cycle], shareholder) == 0;
        
        // //how to =>
        // aborts_if table::contains(pool.pending_withdrawals, delegator);
        
        // ensures old(pool).inactive_shares[lockup_cycle].total_coins - redeemed_coins (result) == 0;
        // aborts_if table::contains(pool.inactive_shares, lockup_cycle);

        // ensures table::contains(old(pool.pending_withdrawals), delegator) && !table::contains(pool.pending_withdrawals, delegator);
        // ensures old(pool.pending_withdrawals)[delegator] == lockup_cycle;

    }

    spec calculate_stake_pool_drift(pool: &DelegationPool): (bool, u64, u64, u64, u64) {
        pragma verify = false;
    }

    spec fun spec_get_pending_inactive(pool: DelegationPool):u64 {
        let pool_address = pool.stake_pool_signer_cap.account;
        let stake_pool = global<stake::StakePool>(pool_address);
        let inactive = stake_pool.inactive.value;
        // let lockup_cycle_ended = inactive > pool.total_coins_inactive;

        if (inactive > pool.total_coins_inactive) {
            // `inactive` on stake pool = any previous `inactive` stake +
            // any previous `pending_inactive` stake and its rewards (both inactivated)
            inactive - pool.total_coins_inactive
        }else {
            0
        }
    }

    spec synchronize_delegation_pool(pool_address: address) {
            pragma verify = true;
            pragma aborts_if_is_strict = false;

            // 1. total_coins(pool.active_shares) == active + pending_active on StakePool
            // let post pool = global<DelegationPool>(pool_address).active_shares;
            // let stake_pool = global<stake::StakePool>(pool_address);

            // let active = stake_pool.active.value;
            // let pending_active = stake_pool.pending_active.value;
            // ensures pool.total_coins == active + pending_active;

            // 2. total_coins(pool.inactive_shares[pool.OLC]) == pending_inactive on StakePool
            // let post pool = global<DelegationPool>(pool_address);
            // let pending_inactive = spec_get_pending_inactive(pool);
            // let pool1 = table::spec_get(pool.inactive_shares,pool.observed_lockup_cycle);
            // ensures pool1.total_coins == pending_inactive;

            // 3. pool.total_coins_inactive == inactive on StakePool
            // let post pool = global<DelegationPool>(pool_address);
            // let pre_pool = global<DelegationPool>(pool_address);
            // let stake_pool = global<stake::StakePool>(pool_address);
            // let inactive = stake_pool.inactive.value;
            // ensures inactive > pre_pool.total_coins_inactive && pool.total_coins_inactive == inactive;

            // 4. inactive > old(total_coins_inactive) IFF pool.OLC == old(pool).OLC + 1:
            // let post pool = global<DelegationPool>(pool_address);
            // let pre_pool = global<DelegationPool>(pool_address);
            // let stake_pool = global<stake::StakePool>(pool_address);
            // let inactive = stake_pool.inactive.value;
            // ensures pre_pool.observed_lockup_cycle.index != pool.observed_lockup_cycle.index && inactive > pre_pool.total_coins_inactive;
            // 5.
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
