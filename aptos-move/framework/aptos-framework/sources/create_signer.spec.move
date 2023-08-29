spec aptos_framework::create_signer {
    use std::signer;

    spec module {
        pragma verify = true;
        pragma aborts_if_is_strict;
    }

    /// Convert address to singer and return.
    spec create_signer(addr: address): signer {
        pragma opaque;
        aborts_if [abstract] false;
        // property 4: A signer should be returned for addresses that are not registered as accounts.
        ensures [abstract] signer::address_of(result) == addr;
    }
}
