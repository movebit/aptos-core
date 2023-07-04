spec aptos_framework::aptos_governance {
    spec module {
        // TODO: Enable this spec when smart_table is supported.
        pragma verify = true;
        pragma aborts_if_is_strict;
    }

    spec store_signer_cap(
        aptos_framework: &signer,
        signer_address: address,
        signer_cap: SignerCapability,
    ) {
        aborts_if !system_addresses::is_aptos_framework_address(signer::address_of(aptos_framework));
        aborts_if !system_addresses::is_framework_reserved_address(signer_address);

        let signer_caps = global<GovernanceResponsbility>(@aptos_framework).signer_caps;
        let post post_signer_caps = global<GovernanceResponsbility>(@aptos_framework).signer_caps;
        aborts_if exists<GovernanceResponsbility>(@aptos_framework) &&
            simple_map::spec_contains_key(signer_caps, signer_address);
        ensures exists<GovernanceResponsbility>(@aptos_framework);
        ensures simple_map::spec_get(post_signer_caps, signer_address) == signer_cap;
    }

    /// Signer address must be @aptos_framework.
    /// The signer does not allow these resources (GovernanceProposal, GovernanceConfig, GovernanceEvents, VotingRecords, ApprovedExecutionHashes) to exist.
    /// The signer must have an Account.
    /// Limit addition overflow.
    spec initialize(
        aptos_framework: &signer,
        min_voting_threshold: u128,
        required_proposer_stake: u64,
        voting_duration_secs: u64,
    ) {
        let addr = signer::address_of(aptos_framework);
        let register_account = global<account::Account>(addr);

        aborts_if register_account.guid_creation_num + 7 > MAX_U64;
        aborts_if register_account.guid_creation_num + 7 >= account::MAX_GUID_CREATION_NUM;

        include InitializeAbortIf;

        ensures exists<voting::VotingForum<GovernanceProposal>>(addr);
        ensures global<voting::VotingForum<GovernanceProposal>>(addr).next_proposal_id == 0;
        ensures exists<GovernanceConfig>(addr);
        ensures exists<GovernanceEvents>(addr);
        ensures exists<VotingRecords>(addr);
        ensures exists<ApprovedExecutionHashes>(addr);
    }

    /// Signer address must be @aptos_framework.
    /// Abort if structs have already been created.
    spec initialize_partial_voting(
        aptos_framework: &signer,
    ) {
        let addr = signer::address_of(aptos_framework);
        aborts_if addr != @aptos_framework;
        aborts_if exists<VotingRecordsV2>(@aptos_framework);
        ensures exists<VotingRecordsV2>(@aptos_framework);
    }

    spec schema InitializeAbortIf {
        aptos_framework: &signer;
        min_voting_threshold: u128;
        required_proposer_stake: u64;
        voting_duration_secs: u64;

        let addr = signer::address_of(aptos_framework);
        let account = global<account::Account>(addr);
        aborts_if addr != @aptos_framework;
        aborts_if exists<voting::VotingForum<GovernanceProposal>>(addr);
        aborts_if exists<GovernanceConfig>(addr);
        aborts_if exists<GovernanceEvents>(addr);
        aborts_if exists<VotingRecords>(addr);
        aborts_if exists<ApprovedExecutionHashes>(addr);
        aborts_if !exists<account::Account>(addr);
    }

    /// Signer address must be @aptos_framework.
    /// Address @aptos_framework must exist GovernanceConfig and GovernanceEvents.
    spec update_governance_config(
        aptos_framework: &signer,
        min_voting_threshold: u128,
        required_proposer_stake: u64,
        voting_duration_secs: u64,
    ) {
        let addr = signer::address_of(aptos_framework);
        let governance_config = global<GovernanceConfig>(@aptos_framework);

        let post new_governance_config = global<GovernanceConfig>(@aptos_framework);
        aborts_if addr != @aptos_framework;
        aborts_if !exists<GovernanceConfig>(@aptos_framework);
        aborts_if !exists<GovernanceEvents>(@aptos_framework);
        modifies global<GovernanceConfig>(addr);

        ensures new_governance_config.voting_duration_secs == voting_duration_secs;
        ensures new_governance_config.min_voting_threshold == min_voting_threshold;
        ensures new_governance_config.required_proposer_stake == required_proposer_stake;
    }

    spec get_voting_duration_secs(): u64 {
        include AbortsIfNotGovernanceConfig;
        ensures result == global<GovernanceConfig>(@aptos_framework).voting_duration_secs;
    }

    spec get_min_voting_threshold(): u128 {
        include AbortsIfNotGovernanceConfig;
        ensures result == global<GovernanceConfig>(@aptos_framework).min_voting_threshold;
    }

    spec get_required_proposer_stake(): u64 {
        include AbortsIfNotGovernanceConfig;
        ensures result == global<GovernanceConfig>(@aptos_framework).required_proposer_stake;
    }

    spec schema AbortsIfNotGovernanceConfig {
        aborts_if !exists<GovernanceConfig>(@aptos_framework);
    }

    spec has_entirely_voted(stake_pool: address, proposal_id: u64): bool {
        aborts_if !exists<VotingRecords>(@aptos_framework);
        let record_key = RecordKey {
            stake_pool,
            proposal_id,
        };
        let voting_records = global<VotingRecords>(@aptos_framework);
        ensures result == table::spec_contains(voting_records.votes, record_key);
    }

    /// The same as spec of `create_proposal_v2()`.
    spec create_proposal(
        proposer: &signer,
        stake_pool: address,
        execution_hash: vector<u8>,
        metadata_location: vector<u8>,
        metadata_hash: vector<u8>,
    ) {
        use aptos_framework::chain_status;
        pragma verify_duration_estimate = 120;

        requires chain_status::is_operating();
        include CreateProposalAbortsIf;
    }

    spec create_proposal_v2(
        proposer: &signer,
        stake_pool: address,
        execution_hash: vector<u8>,
        metadata_location: vector<u8>,
        metadata_hash: vector<u8>,
        is_multi_step_proposal: bool,
    ) {
        use aptos_framework::chain_status;
        pragma verify_duration_estimate = 120;

        requires chain_status::is_operating();
        include CreateProposalAbortsIf;
    }

    spec create_proposal_v2_impl (
        proposer: &signer,
        stake_pool: address,
        execution_hash: vector<u8>,
        metadata_location: vector<u8>,
        metadata_hash: vector<u8>,
        is_multi_step_proposal: bool,
    ): u64 {
        use aptos_framework::chain_status;
        pragma verify_duration_estimate = 120;

        requires chain_status::is_operating();
        include CreateProposalAbortsIf;
        let voting_forum = global<voting::VotingForum<GovernanceProposal>>(@aptos_framework);
        ensures result == voting_forum.next_proposal_id;
    }

    /// `stake_pool` must exist StakePool.
    /// The delegated voter under the resource StakePool of the stake_pool must be the proposer address.
    /// Address @aptos_framework must exist GovernanceEvents.
    spec schema CreateProposalAbortsIf {
        use aptos_framework::stake;

        proposer: &signer;
        stake_pool: address;
        execution_hash: vector<u8>;
        metadata_location: vector<u8>;
        metadata_hash: vector<u8>;

        include VotingGetDelegatedVoterAbortsIf { sign: proposer };
        include AbortsIfNotGovernanceConfig;

        // verify get_voting_power(stake_pool)
        include GetVotingPowerAbortsIf { pool_address: stake_pool };
        let staking_config = global<staking_config::StakingConfig>(@aptos_framework);
        let allow_validator_set_change = staking_config.allow_validator_set_change;
        let stake_pool_res = global<stake::StakePool>(stake_pool);
        // Three results of get_voting_power(stake_pool)
        let stake_balance_0 = stake_pool_res.active.value + stake_pool_res.pending_active.value + stake_pool_res.pending_inactive.value;
        let stake_balance_1 = stake_pool_res.active.value + stake_pool_res.pending_inactive.value;
        let stake_balance_2 = 0;
        let governance_config = global<GovernanceConfig>(@aptos_framework);
        let required_proposer_stake = governance_config.required_proposer_stake;
        // Comparison of the three results of get_voting_power(stake_pool) and required_proposer_stake
        aborts_if allow_validator_set_change && stake_balance_0 < required_proposer_stake;
        aborts_if !allow_validator_set_change && stake::spec_is_current_epoch_validator(stake_pool) && stake_balance_1 < required_proposer_stake;
        aborts_if !allow_validator_set_change && !stake::spec_is_current_epoch_validator(stake_pool) && stake_balance_2 < required_proposer_stake;

        aborts_if !exists<timestamp::CurrentTimeMicroseconds>(@aptos_framework);
        let current_time = timestamp::spec_now_seconds();
        let proposal_expiration = current_time + governance_config.voting_duration_secs;
        aborts_if stake_pool_res.locked_until_secs < proposal_expiration;

        // verify create_proposal_metadata
        include CreateProposalMetadataAbortsIf;

        let addr = aptos_std::type_info::type_of<AptosCoin>().account_address;
        aborts_if !exists<coin::CoinInfo<AptosCoin>>(addr);
        let maybe_supply = global<coin::CoinInfo<AptosCoin>>(addr).supply;
        let supply = option::spec_borrow(maybe_supply);
        let total_supply = aptos_framework::optional_aggregator::optional_aggregator_value(supply);
        let early_resolution_vote_threshold_value = total_supply / 2 + 1;

        // verify voting::create_proposal_v2
        aborts_if option::spec_is_some(maybe_supply) && governance_config.min_voting_threshold > early_resolution_vote_threshold_value;
        aborts_if len(execution_hash) <= 0;
        aborts_if !exists<voting::VotingForum<GovernanceProposal>>(@aptos_framework);
        let voting_forum = global<voting::VotingForum<GovernanceProposal>>(@aptos_framework);
        let proposal_id = voting_forum.next_proposal_id;
        aborts_if proposal_id + 1 > MAX_U64;
        let post post_voting_forum = global<voting::VotingForum<GovernanceProposal>>(@aptos_framework);
        let post post_next_proposal_id = post_voting_forum.next_proposal_id;
        ensures post_next_proposal_id == proposal_id + 1;
        aborts_if !string::spec_internal_check_utf8(voting::IS_MULTI_STEP_PROPOSAL_KEY);
        aborts_if !string::spec_internal_check_utf8(voting::IS_MULTI_STEP_PROPOSAL_IN_EXECUTION_KEY);
        aborts_if table::spec_contains(voting_forum.proposals, proposal_id);
        ensures table::spec_contains(post_voting_forum.proposals, proposal_id);
        aborts_if !exists<GovernanceEvents>(@aptos_framework);
    }

    spec schema VotingGetDelegatedVoterAbortsIf {
        stake_pool: address;
        sign: signer;

        let addr = signer::address_of(sign);
        let stake_pool_res = global<stake::StakePool>(stake_pool);
        aborts_if !exists<stake::StakePool>(stake_pool);
        aborts_if stake_pool_res.delegated_voter != addr;
    }

    /// stake_pool must exist StakePool.
    /// The delegated voter under the resource StakePool of the stake_pool must be the voter address.
    /// Address @aptos_framework must exist VotingRecords and GovernanceProposal.
    spec vote (
        voter: &signer,
        stake_pool: address,
        proposal_id: u64,
        should_pass: bool,
    ) {
        use aptos_framework::chain_status;
        pragma verify_duration_estimate = 120;

        requires chain_status::is_operating();
        include VoteAbortIf  {
            voting_power: MAX_U64
        };
    }

    /// stake_pool must exist StakePool.
    /// The delegated voter under the resource StakePool of the stake_pool must be the voter address.
    /// Address @aptos_framework must exist VotingRecords and GovernanceProposal.
    /// Address @aptos_framework must exist VotingRecordsV2 if partial_governance_voting flag is enabled.
    spec partial_vote (
        voter: &signer,
        stake_pool: address,
        proposal_id: u64,
        voting_power: u64,
        should_pass: bool,
    ) {
        use aptos_framework::chain_status;
        pragma verify_duration_estimate = 120;

        requires chain_status::is_operating();
        include VoteAbortIf;
    }

    /// stake_pool must exist StakePool.
    /// The delegated voter under the resource StakePool of the stake_pool must be the voter address.
    /// Address @aptos_framework must exist VotingRecords and GovernanceProposal.
    /// Address @aptos_framework must exist VotingRecordsV2 if partial_governance_voting flag is enabled.
    spec vote_internal (
        voter: &signer,
        stake_pool: address,
        proposal_id: u64,
        voting_power: u64,
        should_pass: bool,
    ) {
        use aptos_framework::chain_status;
        pragma verify_duration_estimate = 120;

        requires chain_status::is_operating();
        include VoteAbortIf;
    }

    spec schema VoteAbortIf {
        voter: &signer;
        stake_pool: address;
        proposal_id: u64;
        should_pass: bool;
        voting_power: u64;

        include VotingGetDelegatedVoterAbortsIf { sign: voter };

        let voting_forum = global<voting::VotingForum<GovernanceProposal>>(@aptos_framework);
        let proposal = table::spec_get(voting_forum.proposals, proposal_id);
        let proposal_expiration = proposal.expiration_secs;
        let locked_until_secs = global<stake::StakePool>(stake_pool).locked_until_secs;
        aborts_if proposal_expiration > locked_until_secs;

        include GetRemainingVotingPowerAbortsIf;

        let remaining_power = spec_get_remaining_voting_power(stake_pool, proposal_id);
        let real_voting_power = min(voting_power, remaining_power);
        aborts_if !(real_voting_power > 0);

        // verify voting::vote
        aborts_if timestamp::now_seconds() > proposal_expiration;
        aborts_if proposal.is_resolved;
        aborts_if !string::spec_internal_check_utf8(voting::IS_MULTI_STEP_PROPOSAL_IN_EXECUTION_KEY);
        let execution_key = utf8(voting::IS_MULTI_STEP_PROPOSAL_IN_EXECUTION_KEY);
        aborts_if simple_map::spec_contains_key(proposal.metadata, execution_key) &&
                  simple_map::spec_get(proposal.metadata, execution_key) != std::bcs::to_bytes(false);
        aborts_if if (should_pass) { proposal.yes_votes + real_voting_power > MAX_U128 } else { proposal.no_votes + real_voting_power > MAX_U128 };
        let post post_voting_forum = global<voting::VotingForum<GovernanceProposal>>(@aptos_framework);
        let post post_proposal = table::spec_get(post_voting_forum.proposals, proposal_id);
        aborts_if !string::spec_internal_check_utf8(voting::RESOLVABLE_TIME_METADATA_KEY);
        let key = utf8(voting::RESOLVABLE_TIME_METADATA_KEY);
        ensures simple_map::spec_contains_key(post_proposal.metadata, key);
        ensures simple_map::spec_get(post_proposal.metadata, key) == std::bcs::to_bytes(timestamp::now_seconds());

        let record_key = RecordKey {
            stake_pool,
            proposal_id,
        };
        let voting_records_v2 = global<VotingRecordsV2>(@aptos_framework);
        let used_voting_power = if (smart_table::spec_contains(voting_records_v2.votes, record_key)) {
            smart_table::spec_get(voting_records_v2.votes, record_key)
        } else {
            0
        };
        let post post_voting_records_v2 = global<VotingRecordsV2>(@aptos_framework);
        let post post_used_voting_power = smart_table::spec_get(post_voting_records_v2.votes, record_key);
        let voting_records = global<VotingRecords>(@aptos_framework);
        let post post_voting_records = global<VotingRecords>(@aptos_framework);
        aborts_if features::spec_partial_governance_voting_enabled() && used_voting_power + real_voting_power > MAX_U64;
        aborts_if !features::spec_partial_governance_voting_enabled() && !exists<VotingRecords>(@aptos_framework);
        aborts_if !features::spec_partial_governance_voting_enabled() && table::spec_contains(voting_records.votes, record_key);
        ensures if (features::spec_partial_governance_voting_enabled()) {
            post_used_voting_power == used_voting_power + real_voting_power
        } else {
            table::spec_get(post_voting_records.votes, record_key) == true
        };
        
        aborts_if !exists<GovernanceEvents>(@aptos_framework);
        
        // verify voting::get_proposal_state
        let early_resolution_threshold = option::spec_borrow(proposal.early_resolution_vote_threshold);
        let is_voting_period_over = timestamp::spec_now_seconds() > proposal_expiration;

        let new_proposal_yes_votes_0 = proposal.yes_votes + real_voting_power;
        let can_be_resolved_early_0 = option::spec_is_some(proposal.early_resolution_vote_threshold) &&
                                    (new_proposal_yes_votes_0 >= early_resolution_threshold ||
                                     proposal.no_votes >= early_resolution_threshold);
        let is_voting_closed_0 = is_voting_period_over || can_be_resolved_early_0;
        let proposal_state_successed_0 = is_voting_closed_0 && new_proposal_yes_votes_0 > proposal.no_votes &&
                                         new_proposal_yes_votes_0 + proposal.no_votes >= proposal.min_vote_threshold;
        let new_proposal_no_votes_0 = proposal.no_votes + real_voting_power;
        let can_be_resolved_early_1 = option::spec_is_some(proposal.early_resolution_vote_threshold) &&
                                    (proposal.yes_votes >= early_resolution_threshold ||
                                     new_proposal_no_votes_0 >= early_resolution_threshold);
        let is_voting_closed_1 = is_voting_period_over || can_be_resolved_early_1;
        let proposal_state_successed_1 = is_voting_closed_1 && proposal.yes_votes > new_proposal_no_votes_0 &&
                                         proposal.yes_votes + new_proposal_no_votes_0 >= proposal.min_vote_threshold;
        // post state
        let post can_be_resolved_early = option::spec_is_some(proposal.early_resolution_vote_threshold) &&
                                    (post_proposal.yes_votes >= early_resolution_threshold ||
                                     post_proposal.no_votes >= early_resolution_threshold);
        let post is_voting_closed = is_voting_period_over || can_be_resolved_early;
        let post proposal_state_successed = is_voting_closed && post_proposal.yes_votes > post_proposal.no_votes &&
                                         post_proposal.yes_votes + post_proposal.no_votes >= proposal.min_vote_threshold;

        // verify add_approved_script_hash(proposal_id)
        let execution_hash = proposal.execution_hash;
        let post post_approved_hashes = global<ApprovedExecutionHashes>(@aptos_framework);
        aborts_if if (should_pass) {
                proposal_state_successed_0 && !exists<ApprovedExecutionHashes>(@aptos_framework)
            } else {
                proposal_state_successed_1 && !exists<ApprovedExecutionHashes>(@aptos_framework)
            };
        ensures proposal_state_successed ==> simple_map::spec_contains_key(post_approved_hashes.hashes, proposal_id) &&
                                             simple_map::spec_get(post_approved_hashes.hashes, proposal_id) == execution_hash;
    }

    spec add_approved_script_hash(proposal_id: u64) {
        use aptos_framework::chain_status;

        requires chain_status::is_operating();
        include AddApprovedScriptHash;
    }

    spec add_approved_script_hash_script(proposal_id: u64) {
        use aptos_framework::chain_status;

        requires chain_status::is_operating();
        include AddApprovedScriptHash;
    }

    spec schema AddApprovedScriptHash {
        proposal_id: u64;
        aborts_if !exists<ApprovedExecutionHashes>(@aptos_framework);

        aborts_if !exists<voting::VotingForum<GovernanceProposal>>(@aptos_framework);
        let voting_forum = global<voting::VotingForum<GovernanceProposal>>(@aptos_framework);
        let proposal = table::spec_get(voting_forum.proposals, proposal_id);
        aborts_if !table::spec_contains(voting_forum.proposals, proposal_id);
        let early_resolution_threshold = option::spec_borrow(proposal.early_resolution_vote_threshold);
        // The following aborts_if statement is equivalent to aborts_if proposal_state == PROPOSAL_STATE_FAILED or PROPOSAL_STATE_PENDING.
        aborts_if timestamp::now_seconds() <= proposal.expiration_secs &&
            (option::spec_is_none(proposal.early_resolution_vote_threshold) ||
            proposal.yes_votes < early_resolution_threshold && proposal.no_votes < early_resolution_threshold);
        aborts_if (timestamp::now_seconds() > proposal.expiration_secs ||
            option::spec_is_some(proposal.early_resolution_vote_threshold) && (proposal.yes_votes >= early_resolution_threshold ||
                                                                               proposal.no_votes >= early_resolution_threshold)) &&
            (proposal.yes_votes <= proposal.no_votes || proposal.yes_votes + proposal.no_votes < proposal.min_vote_threshold);

        let post post_approved_hashes = global<ApprovedExecutionHashes>(@aptos_framework);
        ensures simple_map::spec_contains_key(post_approved_hashes.hashes, proposal_id) &&
            simple_map::spec_get(post_approved_hashes.hashes, proposal_id) == proposal.execution_hash;
    }

    /// Address @aptos_framework must exist ApprovedExecutionHashes and GovernanceProposal and GovernanceResponsbility.
    spec resolve(proposal_id: u64, signer_address: address): signer {
        use aptos_framework::chain_status;

        requires chain_status::is_operating();

        // verify voting::resolve
        include VotingIsProposalResolvableAbortsif;

        let voting_forum = global<voting::VotingForum<GovernanceProposal>>(@aptos_framework);
        let proposal = table::spec_get(voting_forum.proposals, proposal_id);

        let multi_step_key = utf8(voting::IS_MULTI_STEP_PROPOSAL_KEY);
        let has_multi_step_key = simple_map::spec_contains_key(proposal.metadata, multi_step_key);
        let is_multi_step_proposal = aptos_std::from_bcs::deserialize<bool>(simple_map::spec_get(proposal.metadata, multi_step_key));
        aborts_if has_multi_step_key && !aptos_std::from_bcs::deserializable<bool>(simple_map::spec_get(proposal.metadata, multi_step_key));
        aborts_if !string::spec_internal_check_utf8(voting::IS_MULTI_STEP_PROPOSAL_KEY);
        aborts_if has_multi_step_key && is_multi_step_proposal;

        let post post_voting_forum = global<voting::VotingForum<GovernanceProposal>>(@aptos_framework);
        let post post_proposal = table::spec_get(post_voting_forum.proposals, proposal_id);
        ensures post_proposal.is_resolved == true && post_proposal.resolution_time_secs == timestamp::now_seconds();
        aborts_if option::spec_is_none(proposal.execution_content);

        // verify remove_approved_hash
        aborts_if !exists<ApprovedExecutionHashes>(@aptos_framework);
        let post post_approved_hashes = global<ApprovedExecutionHashes>(@aptos_framework).hashes;
        ensures !simple_map::spec_contains_key(post_approved_hashes, proposal_id);

        // verify get_signer
        include GetSignerAbortsIf;
        let governance_responsibility = global<GovernanceResponsbility>(@aptos_framework);
        let signer_cap = simple_map::spec_get(governance_responsibility.signer_caps, signer_address);
        let addr = signer_cap.account;
        ensures signer::address_of(result) == addr;
    }

    /// Address @aptos_framework must exist ApprovedExecutionHashes and GovernanceProposal.
    spec remove_approved_hash(proposal_id: u64) {
        include voting::AbortsIfNotContainProposalID<GovernanceProposal> { voting_forum_address: @aptos_framework };
        let voting_forum = global<voting::VotingForum<GovernanceProposal>>(@aptos_framework);
        let proposal = table::spec_get(voting_forum.proposals, proposal_id);
        aborts_if !proposal.is_resolved;

        let post approved_hashes = global<ApprovedExecutionHashes>(@aptos_framework).hashes;
        aborts_if !exists<ApprovedExecutionHashes>(@aptos_framework);
        ensures !simple_map::spec_contains_key(approved_hashes, proposal_id);
    }

    spec reconfigure(aptos_framework: &signer) {
        use aptos_framework::chain_status;
        use aptos_framework::coin::CoinInfo;
        use aptos_framework::aptos_coin::AptosCoin;
        use aptos_framework::transaction_fee;

        aborts_if !system_addresses::is_aptos_framework_address(signer::address_of(aptos_framework));

        include transaction_fee::RequiresCollectedFeesPerValueLeqBlockAptosSupply;
        requires chain_status::is_operating();
        requires exists<stake::ValidatorFees>(@aptos_framework);
        requires exists<CoinInfo<AptosCoin>>(@aptos_framework);
        requires exists<staking_config::StakingRewardsConfig>(@aptos_framework);
        include staking_config::StakingRewardsConfigRequirement;

        let current_time = timestamp::spec_now_microseconds();
        let config_ref = global<reconfiguration::Configuration>(@aptos_framework);
        let collected_fees = global<transaction_fee::CollectedFeesPerBlock>(@aptos_framework);
        let post post_collected_fees = global<transaction_fee::CollectedFeesPerBlock>(@aptos_framework);
        let amount = aptos_framework::aggregator::spec_aggregator_get_val(collected_fees.amount.value);
        let post post_amount = aptos_framework::aggregator::spec_aggregator_get_val(post_collected_fees.amount.value);
        let cond = !chain_status::is_genesis() && timestamp::now_microseconds() != 0 && reconfiguration::reconfiguration_enabled()
            && current_time != config_ref.last_reconfiguration_time;
        let proposer = option::spec_borrow(collected_fees.proposer);
        let fees_table = global<stake::ValidatorFees>(@aptos_framework).fees_table;
        let post post_fees_table = global<stake::ValidatorFees>(@aptos_framework).fees_table;
        let fee = amount - amount * collected_fees.burn_percentage / 100;
        ensures cond && features::spec_is_enabled(features::COLLECT_AND_DISTRIBUTE_GAS_FEES)
            && exists<transaction_fee::CollectedFeesPerBlock>(@aptos_framework) ==> 
            post_amount == 0 && option::spec_is_none(post_collected_fees.proposer);
        ensures cond && features::spec_is_enabled(features::COLLECT_AND_DISTRIBUTE_GAS_FEES)
            && exists<transaction_fee::CollectedFeesPerBlock>(@aptos_framework) && amount != 0 && option::spec_is_some(collected_fees.proposer)
            && proposer != @vm_reserved ==> if (table::spec_contains(fees_table, proposer)) {
                table::spec_get(post_fees_table, proposer).value == table::spec_get(fees_table, proposer).value + fee
            } else {
                table::spec_get(post_fees_table, proposer).value == fee
            };
        
        let post validator_set = global<stake::ValidatorSet>(@aptos_framework);
        ensures cond ==> validator_set.pending_inactive == vector::empty();

        let post post_config_ref = global<reconfiguration::Configuration>(@aptos_framework);
        ensures cond ==> post_config_ref.last_reconfiguration_time == current_time && post_config_ref.epoch == config_ref.epoch + 1;
    }

    /// Signer address must be @core_resources.
    /// signer must exist in MintCapStore.
    /// Address @aptos_framework must exist GovernanceResponsbility.
    spec get_signer_testnet_only(core_resources: &signer, signer_address: address): signer {
        aborts_if signer::address_of(core_resources) != @core_resources;
        aborts_if !exists<aptos_coin::MintCapStore>(signer::address_of(core_resources));
        include GetSignerAbortsIf;
        let governance_responsibility = global<GovernanceResponsbility>(@aptos_framework);
        let signer_cap = simple_map::spec_get(governance_responsibility.signer_caps, signer_address);
        ensures signer::address_of(result) == signer_cap.account;
    }

    /// Address @aptos_framework must exist StakingConfig.
    /// limit addition overflow.
    /// pool_address must exist in StakePool.
    spec get_voting_power(pool_address: address): u64 {
        include GetVotingPowerAbortsIf;

        let staking_config = global<staking_config::StakingConfig>(@aptos_framework);
        let allow_validator_set_change = staking_config.allow_validator_set_change;
        let stake_pool_res = global<stake::StakePool>(pool_address);

        ensures allow_validator_set_change ==> result == stake_pool_res.active.value + stake_pool_res.pending_active.value + stake_pool_res.pending_inactive.value;
        ensures !allow_validator_set_change ==> if (stake::spec_is_current_epoch_validator(pool_address)) {
            result == stake_pool_res.active.value + stake_pool_res.pending_inactive.value
        } else {
            result == 0
        };
        ensures result == spec_get_voting_power(pool_address, staking_config);
    }

    spec fun spec_get_voting_power(pool_address: address, staking_config: staking_config::StakingConfig): u64 {
        let allow_validator_set_change = staking_config.allow_validator_set_change;
        let stake_pool_res = global<stake::StakePool>(pool_address);
        if (allow_validator_set_change) {
            stake_pool_res.active.value + stake_pool_res.pending_active.value + stake_pool_res.pending_inactive.value
        } else if (!allow_validator_set_change && (stake::spec_is_current_epoch_validator(pool_address))) {
            stake_pool_res.active.value + stake_pool_res.pending_inactive.value
        } else {
            0
        }
    }

    spec get_remaining_voting_power(stake_pool: address, proposal_id: u64): u64 {
        include GetRemainingVotingPowerAbortsIf;
        
        ensures result == spec_get_remaining_voting_power(stake_pool, proposal_id);
    }

    spec schema GetRemainingVotingPowerAbortsIf {
        stake_pool: address;
        proposal_id: u64;

        aborts_if features::spec_partial_governance_voting_enabled() && !exists<VotingRecordsV2>(@aptos_framework);
        include voting::AbortsIfNotContainProposalID<GovernanceProposal> {
            voting_forum_address: @aptos_framework
        };
        aborts_if !exists<stake::StakePool>(stake_pool);
        aborts_if spec_proposal_expiration <= locked_until && !exists<timestamp::CurrentTimeMicroseconds>(@aptos_framework);
        let spec_proposal_expiration = voting::spec_get_proposal_expiration_secs<GovernanceProposal>(@aptos_framework, proposal_id);
        let locked_until = global<stake::StakePool>(stake_pool).locked_until_secs;
        let remain_zero_1_cond = (spec_proposal_expiration > locked_until || timestamp::spec_now_seconds() > spec_proposal_expiration);
        let record_key = RecordKey {
            stake_pool,
            proposal_id,
        };
        let entirely_voted = spec_has_entirely_voted(stake_pool, proposal_id, record_key);
        aborts_if !remain_zero_1_cond && !exists<VotingRecords>(@aptos_framework);
        include !remain_zero_1_cond && !entirely_voted ==> GetVotingPowerAbortsIf {
            pool_address: stake_pool
        };
        
        let staking_config = global<staking_config::StakingConfig>(@aptos_framework);
        let voting_power = spec_get_voting_power(stake_pool, staking_config);
        let voting_records_v2 = borrow_global<VotingRecordsV2>(@aptos_framework);
        let used_voting_power = if (smart_table::spec_contains(voting_records_v2.votes, record_key)) {
            smart_table::spec_get(voting_records_v2.votes, record_key)
        } else {
            0
        };
        aborts_if !remain_zero_1_cond && !entirely_voted && features::spec_partial_governance_voting_enabled() &&
            used_voting_power > 0 && voting_power < used_voting_power;
    }

    spec fun spec_get_remaining_voting_power(stake_pool: address, proposal_id: u64): u64 {
        let spec_proposal_expiration = voting::spec_get_proposal_expiration_secs<GovernanceProposal>(@aptos_framework, proposal_id);
        let locked_until = global<stake::StakePool>(stake_pool).locked_until_secs;
        let remain_zero_1_cond = (spec_proposal_expiration > locked_until || timestamp::spec_now_seconds() > spec_proposal_expiration);
        let staking_config = global<staking_config::StakingConfig>(@aptos_framework);
        let voting_records_v2 = borrow_global<VotingRecordsV2>(@aptos_framework);
        let record_key = RecordKey {
            stake_pool,
            proposal_id,
        };
        let entirely_voted = spec_has_entirely_voted(stake_pool, proposal_id, record_key);
        let voting_power = spec_get_voting_power(stake_pool, staking_config);
        let used_voting_power = if (smart_table::spec_contains(voting_records_v2.votes, record_key)) {
            smart_table::spec_get(voting_records_v2.votes, record_key)
        } else {
            0
        };
        if (remain_zero_1_cond) {
            0
        } else if (entirely_voted) {
            0
        } else if (!features::spec_partial_governance_voting_enabled()) {
            voting_power
        } else {
            voting_power - used_voting_power
        }
    }

    spec fun spec_has_entirely_voted(stake_pool: address, proposal_id: u64, record_key: RecordKey): bool {
        let voting_records = global<VotingRecords>(@aptos_framework);
        table::spec_contains(voting_records.votes, record_key)
    }

    spec schema GetVotingPowerAbortsIf {
        pool_address: address;

        let staking_config = global<staking_config::StakingConfig>(@aptos_framework);
        aborts_if !exists<staking_config::StakingConfig>(@aptos_framework);
        let allow_validator_set_change = staking_config.allow_validator_set_change;
        let stake_pool_res = global<stake::StakePool>(pool_address);
        aborts_if allow_validator_set_change && (stake_pool_res.active.value + stake_pool_res.pending_active.value + stake_pool_res.pending_inactive.value) > MAX_U64;
        aborts_if !exists<stake::StakePool>(pool_address);
        aborts_if !allow_validator_set_change && !exists<stake::ValidatorSet>(@aptos_framework);
        aborts_if !allow_validator_set_change && stake::spec_is_current_epoch_validator(pool_address) && stake_pool_res.active.value + stake_pool_res.pending_inactive.value > MAX_U64;
    }

    spec get_signer(signer_address: address): signer {
        include GetSignerAbortsIf;
        let governance_responsibility = global<GovernanceResponsbility>(@aptos_framework);
        let signer_cap = simple_map::spec_get(governance_responsibility.signer_caps, signer_address);
        ensures signer::address_of(result) == signer_cap.account;
    }

    spec schema GetSignerAbortsIf {
        signer_address: address;

        aborts_if !exists<GovernanceResponsbility>(@aptos_framework);
        let cap_map = global<GovernanceResponsbility>(@aptos_framework).signer_caps;
        aborts_if !simple_map::spec_contains_key(cap_map, signer_address);
    }

    spec create_proposal_metadata(metadata_location: vector<u8>, metadata_hash: vector<u8>): SimpleMap<String, vector<u8>> {
        include CreateProposalMetadataAbortsIf;

        ensures simple_map::spec_len(result) == 2;
        ensures simple_map::spec_get(result, utf8(METADATA_LOCATION_KEY)) == metadata_location;
        ensures simple_map::spec_get(result, utf8(METADATA_HASH_KEY)) == metadata_hash;
    }

    spec schema CreateProposalMetadataAbortsIf {
        metadata_location: vector<u8>;
        metadata_hash: vector<u8>;

        aborts_if string::length(utf8(metadata_location)) > 256;
        aborts_if string::length(utf8(metadata_hash)) > 256;
        aborts_if !string::spec_internal_check_utf8(metadata_location);
        aborts_if !string::spec_internal_check_utf8(metadata_hash);
        aborts_if !string::spec_internal_check_utf8(METADATA_LOCATION_KEY);
        aborts_if !string::spec_internal_check_utf8(METADATA_HASH_KEY);
    }

    /// verify_only
    spec initialize_for_verification(
        aptos_framework: &signer,
        min_voting_threshold: u128,
        required_proposer_stake: u64,
        voting_duration_secs: u64,
    ) {
        pragma verify = false;
    }

    spec resolve_multi_step_proposal(proposal_id: u64, signer_address: address, next_execution_hash: vector<u8>): signer {
        use aptos_framework::chain_status;
        requires chain_status::is_operating();

        // verify voting::resolve_proposal_v2
        include VotingIsProposalResolvableAbortsif;

        let voting_forum = global<voting::VotingForum<GovernanceProposal>>(@aptos_framework);
        let proposal = table::spec_get(voting_forum.proposals, proposal_id);
        let post post_voting_forum = global<voting::VotingForum<GovernanceProposal>>(@aptos_framework);
        let post post_proposal = table::spec_get(post_voting_forum.proposals, proposal_id);

        aborts_if !string::spec_internal_check_utf8(voting::IS_MULTI_STEP_PROPOSAL_IN_EXECUTION_KEY);
        let multi_step_in_execution_key = utf8(voting::IS_MULTI_STEP_PROPOSAL_IN_EXECUTION_KEY);
        let post is_multi_step_proposal_in_execution_value = simple_map::spec_get(post_proposal.metadata, multi_step_in_execution_key);
        ensures simple_map::spec_contains_key(proposal.metadata, multi_step_in_execution_key) ==>
            is_multi_step_proposal_in_execution_value == std::bcs::serialize(true);

        aborts_if !string::spec_internal_check_utf8(voting::IS_MULTI_STEP_PROPOSAL_KEY);
        let multi_step_key = utf8(voting::IS_MULTI_STEP_PROPOSAL_KEY);
        aborts_if simple_map::spec_contains_key(proposal.metadata, multi_step_key) &&
                            aptos_std::from_bcs::deserializable<bool>(simple_map::spec_get(proposal.metadata, multi_step_key));
        let is_multi_step = simple_map::spec_contains_key(proposal.metadata, multi_step_key) &&
                            aptos_std::from_bcs::deserialize<bool>(simple_map::spec_get(proposal.metadata, multi_step_key));
        let next_execution_hash_is_empty = len(next_execution_hash) == 0;
        aborts_if !is_multi_step && !next_execution_hash_is_empty;
        aborts_if next_execution_hash_is_empty && is_multi_step && !simple_map::spec_contains_key(proposal.metadata, multi_step_in_execution_key); // ?
        ensures next_execution_hash_is_empty ==> post_proposal.is_resolved == true && post_proposal.resolution_time_secs == timestamp::spec_now_seconds() &&
            if (is_multi_step) {
                is_multi_step_proposal_in_execution_value == std::bcs::serialize(false)
            } else {
                simple_map::spec_contains_key(proposal.metadata, multi_step_in_execution_key) ==>
                    is_multi_step_proposal_in_execution_value == std::bcs::serialize(true)
            };
        ensures !next_execution_hash_is_empty ==> post_proposal.execution_hash == next_execution_hash &&
            simple_map::spec_contains_key(proposal.metadata, multi_step_in_execution_key) ==>
                is_multi_step_proposal_in_execution_value == std::bcs::serialize(true);

        // verify remove_approved_hash
        aborts_if next_execution_hash_is_empty && !exists<ApprovedExecutionHashes>(@aptos_framework);
        let post post_approved_hashes = global<ApprovedExecutionHashes>(@aptos_framework).hashes;
        ensures next_execution_hash_is_empty ==> !simple_map::spec_contains_key(post_approved_hashes, proposal_id);
        ensures !next_execution_hash_is_empty ==>
            simple_map::spec_get(post_approved_hashes, proposal_id) == next_execution_hash;

        // verify get_signer
        include GetSignerAbortsIf;
        let governance_responsibility = global<GovernanceResponsbility>(@aptos_framework);
        let signer_cap = simple_map::spec_get(governance_responsibility.signer_caps, signer_address);
        let addr = signer_cap.account;
        ensures signer::address_of(result) == addr;
    }

    spec schema VotingIsProposalResolvableAbortsif {
        proposal_id: u64;

        aborts_if !exists<voting::VotingForum<GovernanceProposal>>(@aptos_framework);
        let voting_forum = global<voting::VotingForum<GovernanceProposal>>(@aptos_framework);
        let proposal = table::spec_get(voting_forum.proposals, proposal_id);
        aborts_if !table::spec_contains(voting_forum.proposals, proposal_id);
        let early_resolution_threshold = option::spec_borrow(proposal.early_resolution_vote_threshold);
        let voting_period_over = timestamp::now_seconds() > proposal.expiration_secs;
        let be_resolved_early = option::spec_is_some(proposal.early_resolution_vote_threshold) &&
                                    (proposal.yes_votes >= early_resolution_threshold ||
                                     proposal.no_votes >= early_resolution_threshold);
        let voting_closed = voting_period_over || be_resolved_early;
        // If Voting Failed
        aborts_if voting_closed && (proposal.yes_votes <= proposal.no_votes || proposal.yes_votes + proposal.no_votes < proposal.min_vote_threshold);
        // If Voting Pending
        aborts_if !voting_closed;

        aborts_if proposal.is_resolved;
        aborts_if !string::spec_internal_check_utf8(voting::RESOLVABLE_TIME_METADATA_KEY);
        aborts_if !simple_map::spec_contains_key(proposal.metadata, utf8(voting::RESOLVABLE_TIME_METADATA_KEY));
        let resolvable_time = aptos_std::from_bcs::deserialize<u64>(simple_map::spec_get(proposal.metadata, utf8(voting::RESOLVABLE_TIME_METADATA_KEY)));
        aborts_if !aptos_std::from_bcs::deserializable<u64>(simple_map::spec_get(proposal.metadata, utf8(voting::RESOLVABLE_TIME_METADATA_KEY)));
        aborts_if timestamp::now_seconds() <= resolvable_time;
        aborts_if aptos_framework::transaction_context::spec_get_script_hash() != proposal.execution_hash;
    }

    spec assert_voting_initialization() {
        include VotingInitializationAbortIfs;
    }

    spec schema VotingInitializationAbortIfs {
        aborts_if features::spec_partial_governance_voting_enabled() && !exists<VotingRecordsV2>(@aptos_framework);
    }
}
