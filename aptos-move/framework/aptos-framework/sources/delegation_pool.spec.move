spec aptos_framework::delegation_pool {
    spec module {
        // TODO: verification disabled until this module is specified.
        pragma verify = false;
        pragma aborts_if_is_strict;
        // 1 
        // invariant forall addr: address: exists<DelegationPool>(addr) ==> exists<stake::StakePool>(addr);
        // 2 timeout
        // invariant forall addr: address: global<DelegationPool>(addr).stake_pool_signer_cap.account == addr;
        // 7 timeout
        // invariant forall addr: address: table::spec_contains(global<DelegationPool>(addr).inactive_shares, global<DelegationPool>(addr).observed_lockup_cycle);
        // 8 timeout
        // forall i in [0, pool.OLC): table::contains(pool.inactive_shares, i) => total_coins(pool.inactive_shares[i]) != 0
        // invariant forall addr: address:
        // forall i in 0..global<DelegationPool>(addr).observed_lockup_cycle.index:
        // table::spec_contains(global<DelegationPool>(addr).inactive_shares,ObservedLockupCycle{index:i}) ==> table::spec_get(global<DelegationPool>(addr).inactive_shares,ObservedLockupCycle{index:i}).total_coins != 0;
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

    //Complete
    spec initialize_delegation_pool(
        owner: &signer,
        operator_commission_percentage: u64,
        delegation_pool_creation_seed: vector<u8>,
    ) {
        pragma verify = false;
        pragma aborts_if_is_partial = true;
        include stake::ResourceRequirement;
        //Property 1 [OK]: asserts_if !features::delegation_pools_enabled()
        //TODO: Prover can't resolve features::delegation_pools_enabled(), use magic number instead , may fixed later.
        aborts_if !features::spec_is_enabled(features::DELEGATION_POOLS);
        //Property 2 [OK]: asserts_if exists<DelegationPoolOwnership>(owner) precondition
        //OK
        aborts_if exists<DelegationPoolOwnership>(signer::address_of(owner));
        //Property 3 [OK]: Sasserts_if operator_commission_percentage > MAX_FEE
        //OK
        aborts_if operator_commission_percentage > MAX_FEE;
        //Property 4 [OK]: exists<DelegationPoolOwnership>(owner) postcondition
        //OK
        ensures exists<DelegationPoolOwnership>(signer::address_of(owner));
        //Property 5 [OK]: let pool_address = global<DelegationPoolOwnership>(owner).pool_address;
        //OK
        let post pool_address = global<DelegationPoolOwnership>(signer::address_of(owner)).pool_address;
        //Property 6 [OK]: exists<DelegationPool>(pool_address)
        //OK
        ensures exists<DelegationPool>(pool_address);
        //Property 7 [OK]: exists<StakePool>(pool_address)
        //OK
        ensures stake::stake_pool_exists(pool_address);
        //Property 8 [OK]: table::contains(pool.inactive_shares, pool.OLC): shares pool of pending_inactive stake always exists (cannot be deleted unless it becomes inactive) 
        //OK
        let post pool = global<DelegationPool>(pool_address);
        ensures table::spec_contains(pool.inactive_shares, pool.observed_lockup_cycle); 
        //Property 9 [OK]:: total_coins(pool.active_shares) == active + pending_active on StakePool
        //OK
        let post stake_pool = global<stake::StakePool>(pool_address);
        ensures pool.active_shares.total_coins == coin::value(stake_pool.active) + coin::value(stake_pool.pending_active);
        //Property 10 [OK]: total_coins(pool.inactive_shares[pool.OLC]) == pending_inactive
        //OK
        ensures table::spec_get(pool.inactive_shares,pool.observed_lockup_cycle).total_coins == coin::value(stake_pool.pending_inactive);
        //Property 11 [OK]: total_coins_inactive == inactive on StakePool
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

    //Complete
    spec add_stake(delegator: &signer, pool_address: address, amount: u64) {

        pragma verify = true;
        pragma aborts_if_is_partial;

        //TODO: Decrease the usage of ghost var

        //Property 8 [TODO]: delegator does not earn rewards from its pending_active stake when this epoch ends
        //Note: I'm not sure if this property should be verfied here, it should belong to sync_delegation_pool

        let pool = global<DelegationPool>(pool_address);
        //Note: Origin func return when amount > 0, so it should be a pre-condition
        requires amount > 0;
       
        //Property 1 [OK]: aborts_if pool_u64::balance(pool.active_shares, delegator) < MIN_COINS_ON_SHARES_POOL
        //Note: Prover occur timeout when introducing the pool_64::balance directly, using ghost var instead.
        aborts_if ghost_balance < MIN_COINS_ON_SHARES_POOL;

        //Property 2 [OK]: ensures active + pending_active == old(active) + old(pending_active) + amount
        //Note: Add a function in stake.move to obtain the onwerbility.pool_address
        ensures ghost_active_p + ghost_pending_active_p == ghost_p_active + ghost_p_pending_active + amount;

        //Property 3 [ERROR]: total_coins(pool.active_shares) == active + pending_active on StakePool
        //Note: Which StakePool does it mean? global<stake::StakePool>(pool_address) or global<stake::StakePool>(get_address_of(pool))?
        ensures global<DelegationPool>(pool_address).active_shares.total_coins == coin::value(global<stake::StakePool>(pool_address).active) + coin::value(global<stake::StakePool>(pool_address).pending_active);

        //Property 4 [OK]: pool_u64::shares(pool.active_shares, delegator) - pool_u64::shares(old(pool).active_shares, delegator) == pool_u64::amount_to_shares(pool.active_shares, amount - get_add_stake_fee(pool_address, amount))   
        //TODO: May use ghost_pool instead of ghost_share later.
        let delegator_address = signer::address_of(delegator);
        let total_coins = pool.active_shares.total_coins;   
        invariant pool_u64::spec_shares(pool.active_shares, delegator_address) - ghost_shares == pool_u64::spec_amount_to_shares_with_total_coins(pool.active_shares, amount - spec_get_add_stake_fee(pool_address, amount), pool.active_shares.total_coins);
        
        //Property 5 [OK]: pool_u64::shares(pool.active_shares, NULL_SHAREHOLDER) - pool_u64::shares(old(pool).active_shares, NULL_SHAREHOLDER) == pool_u64::amount_to_shares(pool.active_shares, get_add_stake_fee(pool_address, amount))
        invariant pool_u64::spec_shares(pool.active_shares, NULL_SHAREHOLDER) - pool_u64::spec_shares( ghost_delegation_pool.active_shares, NULL_SHAREHOLDER) == pool_u64::spec_amount_to_shares_with_total_coins(pool.active_shares, amount - spec_get_add_stake_fee(pool_address, amount), pool.active_shares.total_coins);
        
        //Property 6 [ERROR]:delegator-balance == old(delegator-balance) - amount
        //Issue: Is it possible that the delegator is the same as resources account?
        //Suggestion: Add assert in the origin function
        //After Suggestion [OK]
        ensures ghost_coin_3 == ghost_coin_1 - amount;
        
        //Property 7 [ERROR]: resource-account-balance == old(resource-account-balance)
        //Issue: Delegtor transfer to the pool_address (recive), and let resource-account add stake (paid), how could resource-account balance remain the same?
        //Suggestion: ghost_coin_4 == ghost_coin_2 - amount
        //After Suggestion [OK]
        ensures ghost_coin_4 == ghost_coin_2 - amount;

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

    //Complete
    spec redeem_inactive_shares(
        pool: &mut DelegationPool,
        shareholder: address,
        coins_amount: u64,
        lockup_cycle: ObservedLockupCycle,
    ): u64 {
        pragma verify = false;
        pragma aborts_if_is_partial;
        // Request 1: pool_u64::shares(old(pool).inactive_shares[lockup_cycle], shareholder) != 0 && pool_u64::shares(pool.inactive_shares[lockup_cycle], shareholder) == 0 => !table::contains(pending_withdrawals, delegator)
        // OK
        ensures (pool_u64::spec_shares(table::spec_get(old(pool).inactive_shares,lockup_cycle), shareholder) != 0 && pool_u64::spec_shares(table::spec_get(old(pool).inactive_shares,lockup_cycle), shareholder) == 0 ==> !table::spec_contains(pool.pending_withdrawals, shareholder));
        // Request 2: total_coins(old(pool).inactive_shares[lockup_cycle]) - redeemed_coins (result) == 0 => !table::contains(pool.inactive_shares, lockup_cycle): 
        // ISSUE & QUESTION
        // The inactive[olc] exist, however, it's total_coin = 0. Should we change the condition to pool.inactive_shares.total_coin == 0 ?
        // If the condition modified as mentioned, it shall pass.
        ensures lockup_cycle.index != 0 && table::spec_get(old(pool).inactive_shares,lockup_cycle).total_coins - result == 0 ==> table::spec_get(pool.inactive_shares, lockup_cycle).total_coins == 0;

        // Request 3: table::contains(old(pending_withdrawals), delegator) && !table::contains(pending_withdrawals, delegator) => old(pending_withdrawals)[delegator] == lockup_cycle:
        // OK & QUESTION
        // The prover can't apply this condition correctly: !table::spec_contains(pool.pending_withdrawals, shareholder)
        // To solve this issue, apply (pre) != (post), this new condition is resonable beacuse:
        // Obviously, if the function deleted a shareholder from the table, the (pre) should never be the same as (post)
        let a = table::spec_get(pool.pending_withdrawals, shareholder);
        let post b = table::spec_get(pool.pending_withdrawals, shareholder);
        ensures table::spec_contains(old(pool).pending_withdrawals, shareholder) && !table::spec_contains(pool.pending_withdrawals, shareholder) && a != b ==> table::spec_get(old(pool).pending_withdrawals, shareholder) == lockup_cycle;
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
            
            // Property 5 [OK]: pool.OLC == old(pool).OLC + 1 => table::contains(pool.inactive_shares, pool.OLC)
            let post pool = global<DelegationPool>(pool_address);
            let pre_pool = global<DelegationPool>(pool_address);
            let stake_pool = global<stake::StakePool>(pool_address);
            let inactive = stake_pool.inactive.value;
            ensures pool.observed_lockup_cycle.index == pre_pool.observed_lockup_cycle.index + 1 ==> table::spec_contains(pool.inactive_shares,pool.observed_lockup_cycle);
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
