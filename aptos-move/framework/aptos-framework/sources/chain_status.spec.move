spec aptos_framework::chain_status {
    spec module {
        pragma verify = true;
        pragma aborts_if_is_strict;
        // property 2: The status of the chain should never be genesis and operating at the same time.
        invariant is_operating() == !is_genesis();
    }

    spec set_genesis_end {
        include RequiresIsOperating;

        aborts_if std::signer::address_of(aptos_framework) != @aptos_framework;
        // property 3: The status of the chain should only be changed once, from genesis to operating.
        aborts_if exists<GenesisEndMarker>(@aptos_framework);

        ensures exists<GenesisEndMarker>(@aptos_framework);
    }

    spec schema RequiresIsOperating {
        requires is_operating();
    }

    spec assert_operating {
        // property 1: The end of genesis mark should persist throughout the entire life of the chain.
        aborts_if !is_operating();
    }

    spec assert_genesis {
        aborts_if !is_genesis();
    }
}
