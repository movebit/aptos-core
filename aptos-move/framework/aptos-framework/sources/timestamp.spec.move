spec aptos_framework::timestamp {
    spec module {
        use aptos_framework::chain_status;
        // property 1: There should only exist one global wall clock and it should be created during genesis.
        // property 2: The global wall clock resource should only be owned by the Aptos framework.
        invariant chain_status::is_operating() ==> exists<CurrentTimeMicroseconds>(@aptos_framework);
    }

    spec update_global_time {
        use aptos_framework::chain_status;
        requires chain_status::is_operating();
        include UpdateGlobalTimeAbortsIf;

        let old_time = global<CurrentTimeMicroseconds>(@aptos_framework).microseconds;
        let post lastest_time = global<CurrentTimeMicroseconds>(@aptos_framework).microseconds;
        ensures if(proposer == @vm_reserved) {
            lastest_time == old_time
        } else {
            lastest_time == timestamp
        };
    }

    spec schema UpdateGlobalTimeAbortsIf {
        account: signer;
        proposer: address;
        timestamp: u64;
        // property 3: The clock time should only be updated by the VM account.
        aborts_if !system_addresses::is_vm(account);
        // property 4: The clock time should increase with every update as agreed through consensus and proposed by the current epoch's validator.
        aborts_if (proposer == @vm_reserved) && (spec_now_microseconds() != timestamp);
        aborts_if (proposer != @vm_reserved) && (spec_now_microseconds() >= timestamp);
    }

    spec fun spec_now_microseconds(): u64 {
        global<CurrentTimeMicroseconds>(@aptos_framework).microseconds
    }

    spec fun spec_now_seconds(): u64 {
        spec_now_microseconds() / MICRO_CONVERSION_FACTOR
    }
}
