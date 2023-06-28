spec aptos_framework::aptos_coin {
    spec module {
        pragma verify = true;
        pragma aborts_if_is_strict;
    }

    spec initialize {
        use aptos_framework::optional_aggregator::optional_aggregator_value;
        
        let addr = signer::address_of(aptos_framework);
        aborts_if addr != @aptos_framework;
        aborts_if !string::spec_internal_check_utf8(b"Aptos Coin");
        aborts_if !string::spec_internal_check_utf8(b"APT");
        include coin::InitializeInternalSchema<AptosCoin> { account: aptos_framework, name: b"Aptos Coin", symbol: b"APT" };
        aborts_if !exists<aptos_framework::aggregator_factory::AggregatorFactory>(@aptos_framework);
        aborts_if exists<MintCapStore>(addr);

        ensures exists<MintCapStore>(addr);
        ensures exists<coin::CoinInfo<AptosCoin>>(addr);
        ensures optional_aggregator_value(option::spec_borrow(global<coin::CoinInfo<AptosCoin>>(addr).supply)) == 0;
        ensures result_1 == BurnCapability<AptosCoin>{};
        ensures result_2 == MintCapability<AptosCoin>{};
    }

    spec destroy_mint_cap {
        let addr = signer::address_of(aptos_framework);
        aborts_if addr != @aptos_framework;
        aborts_if !exists<MintCapStore>(@aptos_framework);

        ensures !exists<MintCapStore>(@aptos_framework);
    }

    // Test function,not needed verify.
    spec configure_accounts_for_test {
        pragma verify = false;
    }

    // Only callable in tests and testnets.not needed verify.
    spec mint {
        pragma verify = false;
    }

    // Only callable in tests and testnets.not needed verify.
    spec delegate_mint_capability {
        pragma verify = false;
    }

    // Only callable in tests and testnets.not needed verify.
    spec claim_mint_capability(account: &signer) {
        pragma verify = false;
    }

    spec find_delegation(addr: address): Option<u64> {
        aborts_if !exists<Delegations>(@core_resources);

        let delegations = global<Delegations>(@core_resources).inner;
        ensures (exists i in 0..len(delegations): delegations[i].to == addr) ==>
            option::spec_borrow(result) >= 0 && option::spec_borrow(result) < len(delegations);
        ensures (forall i in 0..len(delegations): delegations[i].to != addr) ==>
            option::spec_is_none(result);
    }
}
