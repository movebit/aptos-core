spec aptos_framework::aptos_governance {
    spec module {
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
        aborts_if exists<GovernanceResponsbility>(@aptos_framework) &&
            simple_map::spec_contains_key(signer_caps, signer_address);
        ensures exists<GovernanceResponsbility>(@aptos_framework);
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
        use aptos_std::type_info::Self;

        let addr = signer::address_of(aptos_framework);
        let register_account = global<account::Account>(addr);

        aborts_if exists<voting::VotingForum<GovernanceProposal>>(addr);
        aborts_if !exists<account::Account>(addr);
        aborts_if register_account.guid_creation_num + 7 > MAX_U64;
        aborts_if register_account.guid_creation_num + 7 >= account::MAX_GUID_CREATION_NUM;
        aborts_if !type_info::spec_is_struct<GovernanceProposal>();

        include InitializeAbortIf;

        ensures exists<voting::VotingForum<governance_proposal::GovernanceProposal>>(addr);
        ensures exists<GovernanceConfig>(addr);
        ensures exists<GovernanceEvents>(addr);
        ensures exists<VotingRecords>(addr);
        ensures exists<ApprovedExecutionHashes>(addr);
    }

    spec schema InitializeAbortIf {
        aptos_framework: &signer;
        min_voting_threshold: u128;
        required_proposer_stake: u64;
        voting_duration_secs: u64;

        let addr = signer::address_of(aptos_framework);
        let account = global<account::Account>(addr);
        aborts_if addr != @aptos_framework;
        aborts_if exists<voting::VotingForum<governance_proposal::GovernanceProposal>>(addr);
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
    }

    spec get_min_voting_threshold(): u128 {
        include AbortsIfNotGovernanceConfig;
    }

    spec get_required_proposer_stake(): u64 {
        include AbortsIfNotGovernanceConfig;
    }

    spec schema AbortsIfNotGovernanceConfig {
        aborts_if !exists<GovernanceConfig>(@aptos_framework);
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
        // TODO: Calls `create_proposal_v2`.
        pragma aborts_if_is_partial;
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
        // TODO: The variable `stake_balance` is the return value of the function `get_voting_power`.
        // `get_voting_power` has already stated that it cannot be fully verified,
        // so the value of `stake_balance` cannot be obtained in the spec,
        // and the `aborts_if` of `stake_balancede` cannot be written.
        // pragma aborts_if_is_partial;
        requires chain_status::is_operating();
        // include CreateProposalAbortsIf;
        let proposer_address = signer::address_of(proposer);
        aborts_if !exists<stake::StakePool>(stake_pool);
        aborts_if global<stake::StakePool>(stake_pool).delegated_voter != proposer_address;

        // 242 borrow
        include AbortsIfNotGovernanceConfig;

        // 243 245
        let stake_pool_res = global<stake::StakePool>(stake_pool);
        let staking_config = global<staking_config::StakingConfig>(@aptos_framework);
        let allow_validator_set_change = staking_config.allow_validator_set_change;
        let stake_balance_0 = stake_pool_res.active.value + stake_pool_res.pending_active.value + stake_pool_res.pending_inactive.value;
        let stake_balance_1 = stake_pool_res.active.value + stake_pool_res.pending_inactive.value;
        let stake_balance_2 = 0;
        let governance_config = global<GovernanceConfig>(@aptos_framework);
        aborts_if allow_validator_set_change && stake_balance_0 > MAX_U64;
        aborts_if !allow_validator_set_change && !exists<stake::ValidatorSet>(@aptos_framework);  // stake::get_current_epoch_voting_power(pool_address)
        aborts_if !allow_validator_set_change && stake::spec_is_current_epoch_validator(stake_pool) && stake_balance_1 > MAX_U64;
        aborts_if allow_validator_set_change && stake_balance_0 < governance_config.required_proposer_stake;
        aborts_if !allow_validator_set_change && stake::spec_is_current_epoch_validator(stake_pool) && stake_balance_1 < governance_config.required_proposer_stake;
        aborts_if !allow_validator_set_change && !stake::spec_is_current_epoch_validator(stake_pool) && stake_balance_2 < governance_config.required_proposer_stake;

        // 250 253
        aborts_if !exists<timestamp::CurrentTimeMicroseconds>(@aptos_framework);  // 250
        let current_time = timestamp::now_seconds();
        let proposal_expiration = current_time + governance_config.voting_duration_secs;
        aborts_if stake_pool_res.locked_until_secs < proposal_expiration;  // 253 ?
        
        // 258
        aborts_if !string::spec_internal_check_utf8(metadata_location);
        aborts_if !string::spec_internal_check_utf8(metadata_hash);
        aborts_if !string::spec_internal_check_utf8(METADATA_LOCATION_KEY);
        aborts_if !string::spec_internal_check_utf8(METADATA_HASH_KEY);
        aborts_if string::length(utf8(metadata_location)) > 256;
        aborts_if string::length(utf8(metadata_hash)) > 256;
        // let proposal_metadata = simple_map::create<String, vector<u8>>();
        
        // 264
        let addr = aptos_std::type_info::type_of<AptosCoin>().account_address;
        aborts_if !exists<coin::CoinInfo<AptosCoin>>(addr);  // 264
        let maybe_supply = global<coin::CoinInfo<AptosCoin>>(addr).supply;
        let supply = option::spec_borrow(maybe_supply);
        let total_supply = aptos_framework::optional_aggregator::optional_aggregator_value(supply);
        let early_resolution_vote_threshold_value = total_supply / 2 + 1;
        // let early_resolution_vote_threshold = option::spec_some(total_supply / 2 + 1);

        // 272
        aborts_if early_resolution_vote_threshold_value != 0 && governance_config.min_voting_threshold > early_resolution_vote_threshold_value;
        aborts_if len(execution_hash) == 0;
        aborts_if !exists<voting::VotingForum<GovernanceProposal>>(@aptos_framework);
        let voting_forum = global<voting::VotingForum<GovernanceProposal>>(@aptos_framework);
        let proposal_id = voting_forum.next_proposal_id;
        let old_next_proposal_id = voting_forum.next_proposal_id;
        let post post_next_proposal_id = voting_forum.next_proposal_id;
        aborts_if old_next_proposal_id + 1 > MAX_U64;
        ensures post_next_proposal_id == old_next_proposal_id + 1;
        aborts_if !string::spec_internal_check_utf8(voting::IS_MULTI_STEP_PROPOSAL_KEY);
        aborts_if voting::IS_MULTI_STEP_PROPOSAL_KEY == METADATA_LOCATION_KEY || voting::IS_MULTI_STEP_PROPOSAL_KEY == METADATA_HASH_KEY;
        aborts_if !string::spec_internal_check_utf8(voting::IS_MULTI_STEP_PROPOSAL_IN_EXECUTION_KEY);
        aborts_if is_multi_step_proposal && voting::IS_MULTI_STEP_PROPOSAL_IN_EXECUTION_KEY == METADATA_LOCATION_KEY 
                                         || voting::IS_MULTI_STEP_PROPOSAL_IN_EXECUTION_KEY == METADATA_HASH_KEY 
                                         || voting::IS_MULTI_STEP_PROPOSAL_IN_EXECUTION_KEY == voting::IS_MULTI_STEP_PROPOSAL_KEY;
        aborts_if !is_multi_step_proposal && voting::IS_MULTI_STEP_PROPOSAL_IN_EXECUTION_KEY != METADATA_LOCATION_KEY 
                                          && voting::IS_MULTI_STEP_PROPOSAL_IN_EXECUTION_KEY != METADATA_HASH_KEY 
                                          && voting::IS_MULTI_STEP_PROPOSAL_IN_EXECUTION_KEY != voting::IS_MULTI_STEP_PROPOSAL_KEY;
        aborts_if table::spec_contains(voting_forum.proposals, old_next_proposal_id);
        ensures table::spec_contains(voting_forum.proposals, old_next_proposal_id);

        aborts_if !exists<GovernanceEvents>(@aptos_framework);
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

        /*
        let proposer_address = signer::address_of(proposer);
        let governance_config = global<GovernanceConfig>(@aptos_framework);
        let stake_pool_res = global<stake::StakePool>(stake_pool);
        aborts_if !exists<staking_config::StakingConfig>(@aptos_framework);
        aborts_if !exists<stake::StakePool>(stake_pool);
        aborts_if global<stake::StakePool>(stake_pool).delegated_voter != proposer_address;
        include AbortsIfNotGovernanceConfig;
        let current_time = timestamp::now_seconds();
        let proposal_expiration = current_time + governance_config.voting_duration_secs;
        aborts_if stake_pool_res.locked_until_secs < proposal_expiration;
        */

        // 239 assert
        let proposer_address = signer::address_of(proposer);
        aborts_if !exists<stake::StakePool>(stake_pool);
        aborts_if global<stake::StakePool>(stake_pool).delegated_voter != proposer_address;

        // 242 borrow
        include AbortsIfNotGovernanceConfig;

        // 243 245
        let stake_pool_res = global<stake::StakePool>(stake_pool);
        let staking_config = global<staking_config::StakingConfig>(@aptos_framework);
        let allow_validator_set_change = staking_config.allow_validator_set_change;
        let stake_balance_0 = stake_pool_res.active.value + stake_pool_res.pending_active.value + stake_pool_res.pending_inactive.value;
        let stake_balance_1 = stake_pool_res.active.value + stake_pool_res.pending_inactive.value;
        let stake_balance_2 = 0;
        let governance_config = global<GovernanceConfig>(@aptos_framework);
        aborts_if allow_validator_set_change && stake_balance_0 > MAX_U64;
        aborts_if !allow_validator_set_change && !exists<stake::ValidatorSet>(@aptos_framework);  // stake::get_current_epoch_voting_power(pool_address)
        aborts_if !allow_validator_set_change && stake::spec_is_current_epoch_validator(stake_pool) && stake_balance_1 > MAX_U64;
        aborts_if allow_validator_set_change && stake_balance_0 < governance_config.required_proposer_stake;
        aborts_if !allow_validator_set_change && stake::spec_is_current_epoch_validator(stake_pool) && stake_balance_1 < governance_config.required_proposer_stake;
        aborts_if !allow_validator_set_change && !stake::spec_is_current_epoch_validator(stake_pool) && stake_balance_2 < governance_config.required_proposer_stake;

        // 250 253
        aborts_if !exists<timestamp::CurrentTimeMicroseconds>(@aptos_framework);  // 250
        let current_time = timestamp::now_seconds();
        let proposal_expiration = current_time + governance_config.voting_duration_secs;
        aborts_if stake_pool_res.locked_until_secs < proposal_expiration;  // 253 ?
        
        // 258
        aborts_if !string::spec_internal_check_utf8(metadata_location);
        aborts_if !string::spec_internal_check_utf8(metadata_hash);
        aborts_if !string::spec_internal_check_utf8(METADATA_LOCATION_KEY);
        aborts_if !string::spec_internal_check_utf8(METADATA_HASH_KEY);
        aborts_if string::length(utf8(metadata_location)) > 256;
        aborts_if string::length(utf8(metadata_hash)) > 256;
        
        // 264
        let addr = aptos_std::type_info::type_of<AptosCoin>().account_address;
        aborts_if !exists<coin::CoinInfo<AptosCoin>>(addr);  // 264
        let maybe_supply = global<coin::CoinInfo<AptosCoin>>(addr).supply;
        let supply = option::spec_borrow(maybe_supply);
        let total_supply = aptos_framework::optional_aggregator::optional_aggregator_value(supply);
        let early_resolution_vote_threshold_value = total_supply / 2 + 1;
        // let early_resolution_vote_threshold = option::spec_some(total_supply / 2 + 1);

        /* // 272
        aborts_if early_resolution_vote_threshold_value != 0 && governance_config.min_voting_threshold > early_resolution_vote_threshold_value;
        aborts_if len(execution_hash) == 0;
        aborts_if !exists<voting::VotingForum<GovernanceProposal>>(@aptos_framework);
        let voting_forum = global<voting::VotingForum<GovernanceProposal>>(@aptos_framework);
        let proposal_id = voting_forum.next_proposal_id;
        let old_next_proposal_id = voting_forum.next_proposal_id;
        let post post_next_proposal_id = voting_forum.next_proposal_id;
        aborts_if old_next_proposal_id + 1 > MAX_U64;
        ensures post_next_proposal_id == old_next_proposal_id + 1;
        aborts_if !string::spec_internal_check_utf8(voting::IS_MULTI_STEP_PROPOSAL_KEY);
        aborts_if voting::IS_MULTI_STEP_PROPOSAL_KEY == METADATA_LOCATION_KEY || voting::IS_MULTI_STEP_PROPOSAL_KEY == METADATA_HASH_KEY;
        aborts_if !string::spec_internal_check_utf8(voting::IS_MULTI_STEP_PROPOSAL_IN_EXECUTION_KEY);
        aborts_if is_multi_step_proposal && voting::IS_MULTI_STEP_PROPOSAL_IN_EXECUTION_KEY == METADATA_LOCATION_KEY 
                                         || voting::IS_MULTI_STEP_PROPOSAL_IN_EXECUTION_KEY == METADATA_HASH_KEY 
                                         || voting::IS_MULTI_STEP_PROPOSAL_IN_EXECUTION_KEY == voting::IS_MULTI_STEP_PROPOSAL_KEY;
        aborts_if !is_multi_step_proposal && voting::IS_MULTI_STEP_PROPOSAL_IN_EXECUTION_KEY != METADATA_LOCATION_KEY 
                                          && voting::IS_MULTI_STEP_PROPOSAL_IN_EXECUTION_KEY != METADATA_HASH_KEY 
                                          && voting::IS_MULTI_STEP_PROPOSAL_IN_EXECUTION_KEY != voting::IS_MULTI_STEP_PROPOSAL_KEY;
        aborts_if table::spec_contains(voting_forum.proposals, old_next_proposal_id);
        ensures table::spec_contains(voting_forum.proposals, old_next_proposal_id); */

        aborts_if !exists<GovernanceEvents>(@aptos_framework);
        // let allow_validator_set_change = global<staking_config::StakingConfig>(@aptos_framework).allow_validator_set_change;
        // aborts_if !allow_validator_set_change && !exists<stake::ValidatorSet>(@aptos_framework);
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
        use aptos_framework::stake;
        use aptos_framework::chain_status;

        // TODO: The variable `voting_power` is the return value of the function `get_voting_power`.
        // `get_voting_power` has already stated that it cannot be completely verified,
        // so the value of `voting_power` cannot be obtained in the spec,
        // and the `aborts_if` of `voting_power` cannot be written.
        // pragma aborts_if_is_partial;

        requires chain_status::is_operating();

        let voter_address = signer::address_of(voter);
        let stake_pool_res = global<stake::StakePool>(stake_pool);
        aborts_if !exists<stake::StakePool>(stake_pool);
        aborts_if stake_pool_res.delegated_voter != voter_address;

        aborts_if !exists<VotingRecords>(@aptos_framework);
        let voting_records = global<VotingRecords>(@aptos_framework);
        let record_key = RecordKey {
            stake_pool,
            proposal_id,
        };
        let post post_voting_records = global<VotingRecords>(@aptos_framework);
        aborts_if table::spec_contains(voting_records.votes, record_key);
        ensures table::spec_get(post_voting_records.votes, record_key) == true;

        aborts_if !exists<staking_config::StakingConfig>(@aptos_framework);
        let allow_validator_set_change = global<staking_config::StakingConfig>(@aptos_framework).allow_validator_set_change;
        let voting_power_0 = stake_pool_res.active.value + stake_pool_res.pending_active.value + stake_pool_res.pending_inactive.value;
        let voting_power_1 = stake_pool_res.active.value + stake_pool_res.pending_inactive.value;
        aborts_if allow_validator_set_change && voting_power_0 > MAX_U64;
        aborts_if !allow_validator_set_change && !exists<stake::ValidatorSet>(@aptos_framework);  // stake::get_current_epoch_voting_power(pool_address)
        aborts_if !allow_validator_set_change && stake::spec_is_current_epoch_validator(stake_pool) && voting_power_1 > MAX_U64;
        aborts_if allow_validator_set_change && voting_power_0 <= 0;
        aborts_if !allow_validator_set_change && stake::spec_is_current_epoch_validator(stake_pool) && voting_power_1 <= 0;
        aborts_if !allow_validator_set_change && !stake::spec_is_current_epoch_validator(stake_pool);

        aborts_if !exists<voting::VotingForum<GovernanceProposal>>(@aptos_framework);
        let voting_forum = global<voting::VotingForum<GovernanceProposal>>(@aptos_framework);
        let proposal = table::spec_get(voting_forum.proposals, proposal_id);
        aborts_if !table::spec_contains(voting_forum.proposals, proposal_id);
        let proposal_expiration = proposal.expiration_secs;
        let locked_until_secs = global<stake::StakePool>(stake_pool).locked_until_secs;
        aborts_if proposal_expiration > locked_until_secs;

        aborts_if timestamp::now_seconds() > proposal_expiration;
        aborts_if proposal.is_resolved;
        aborts_if !string::spec_internal_check_utf8(voting::IS_MULTI_STEP_PROPOSAL_IN_EXECUTION_KEY);
        let execution_key = utf8(voting::IS_MULTI_STEP_PROPOSAL_IN_EXECUTION_KEY);
        aborts_if simple_map::spec_contains_key(proposal.metadata, execution_key) &&
                  simple_map::spec_get(proposal.metadata, execution_key) != std::bcs::to_bytes(false);
        aborts_if allow_validator_set_change &&
            if (should_pass) { proposal.yes_votes + voting_power_0 > MAX_U128 } else { proposal.no_votes + voting_power_0 > MAX_U128 };
        aborts_if !allow_validator_set_change &&
            if (should_pass) { proposal.yes_votes + voting_power_1 > MAX_U128 } else { proposal.no_votes + voting_power_1 > MAX_U128 };
        let post post_voting_forum = global<voting::VotingForum<GovernanceProposal>>(@aptos_framework);
        let post post_proposal = table::spec_get(post_voting_forum.proposals, proposal_id);
        ensures allow_validator_set_change ==> 
            if (should_pass) { post_proposal.yes_votes == proposal.yes_votes + voting_power_0 } else { post_proposal.no_votes == proposal.no_votes + voting_power_0 };
        ensures !allow_validator_set_change ==> 
            if (should_pass) { post_proposal.yes_votes == proposal.yes_votes + voting_power_1 } else { post_proposal.no_votes == proposal.no_votes + voting_power_1 };
        aborts_if !string::spec_internal_check_utf8(voting::RESOLVABLE_TIME_METADATA_KEY);
        let key = utf8(voting::RESOLVABLE_TIME_METADATA_KEY);
        ensures simple_map::spec_contains_key(post_proposal.metadata, key);
        ensures simple_map::spec_get(post_proposal.metadata, key) == std::bcs::to_bytes(timestamp::now_seconds());

        aborts_if !exists<GovernanceEvents>(@aptos_framework);

        let early_resolution_threshold = option::spec_borrow(proposal.early_resolution_vote_threshold);
        let is_voting_period_over = timestamp::now_seconds() > proposal_expiration;
        /// allow_validator_set_change && should_pass
        let new_proposal_yes_votes_0 = proposal.yes_votes + voting_power_0;
        let can_be_resolved_early_0 = option::spec_is_some(proposal.early_resolution_vote_threshold) && 
                                    (new_proposal_yes_votes_0 >= early_resolution_threshold ||
                                     proposal.no_votes >= early_resolution_threshold);
        let is_voting_closed_0 = is_voting_period_over || can_be_resolved_early_0;
        let proposal_state_successed_0 = is_voting_closed_0 && new_proposal_yes_votes_0 > proposal.no_votes &&
                                         new_proposal_yes_votes_0 + proposal.no_votes >= proposal.min_vote_threshold;
        /// allow_validator_set_change && !should_pass
        let new_proposal_no_votes_0 = proposal.no_votes + voting_power_0;
        let can_be_resolved_early_1 = option::spec_is_some(proposal.early_resolution_vote_threshold) && 
                                    (proposal.yes_votes >= early_resolution_threshold ||
                                     new_proposal_no_votes_0 >= early_resolution_threshold);
        let is_voting_closed_1 = is_voting_period_over || can_be_resolved_early_1;
        let proposal_state_successed_1 = is_voting_closed_1 && proposal.yes_votes > new_proposal_no_votes_0 &&
                                         proposal.yes_votes + new_proposal_no_votes_0 >= proposal.min_vote_threshold;
        /// !allow_validator_set_change && should_pass
        let new_proposal_yes_votes_1 = proposal.yes_votes + voting_power_1;
        let can_be_resolved_early_2 = option::spec_is_some(proposal.early_resolution_vote_threshold) && 
                                    (new_proposal_yes_votes_1 >= early_resolution_threshold ||
                                     proposal.no_votes >= early_resolution_threshold);
        let is_voting_closed_2 = is_voting_period_over || can_be_resolved_early_2;
        let proposal_state_successed_2 = is_voting_closed_2 && new_proposal_yes_votes_1 > proposal.no_votes &&
                                         new_proposal_yes_votes_1 + proposal.no_votes >= proposal.min_vote_threshold;
        /// !allow_validator_set_change && !should_pass
        let new_proposal_no_votes_1 = proposal.no_votes + voting_power_1;
        let can_be_resolved_early_3 = option::spec_is_some(proposal.early_resolution_vote_threshold) && 
                                    (proposal.yes_votes >= early_resolution_threshold ||
                                     new_proposal_no_votes_1 >= early_resolution_threshold);               
        let is_voting_closed_3 = is_voting_period_over || can_be_resolved_early_3;
        let proposal_state_successed_3 = is_voting_closed_3 && proposal.yes_votes > new_proposal_no_votes_1 &&
                                         proposal.yes_votes + new_proposal_no_votes_1 >= proposal.min_vote_threshold;
        /// post
        let post can_be_resolved_early = option::spec_is_some(proposal.early_resolution_vote_threshold) && 
                                    (post_proposal.yes_votes >= early_resolution_threshold ||
                                     post_proposal.no_votes >= early_resolution_threshold);
        let post is_voting_closed = is_voting_period_over || can_be_resolved_early;
        let post proposal_state_successed = is_voting_closed && post_proposal.yes_votes > post_proposal.no_votes &&
                                         post_proposal.yes_votes + post_proposal.no_votes >= proposal.min_vote_threshold;
        let execution_hash = proposal.execution_hash;
        let post post_approved_hashes = global<ApprovedExecutionHashes>(@aptos_framework);
        // aborts_if allow_validator_set_change && should_pass && proposal_state_successed_0 && !exists<ApprovedExecutionHashes>(@aptos_framework);
        // aborts_if allow_validator_set_change && !should_pass && proposal_state_successed_1 && !exists<ApprovedExecutionHashes>(@aptos_framework);
        // aborts_if !allow_validator_set_change && should_pass && proposal_state_successed_2 && !exists<ApprovedExecutionHashes>(@aptos_framework);
        // aborts_if !allow_validator_set_change && !should_pass && proposal_state_successed_3 && !exists<ApprovedExecutionHashes>(@aptos_framework);
        aborts_if allow_validator_set_change && 
            if (should_pass) {
                proposal_state_successed_0 && !exists<ApprovedExecutionHashes>(@aptos_framework)
            } else {
                proposal_state_successed_1 && !exists<ApprovedExecutionHashes>(@aptos_framework)
            };
        aborts_if !allow_validator_set_change &&
            if (should_pass) {
                proposal_state_successed_2 && !exists<ApprovedExecutionHashes>(@aptos_framework)
            } else {
                proposal_state_successed_3 && !exists<ApprovedExecutionHashes>(@aptos_framework)
            };
        /*ensures timestamp::now_seconds() > proposal_expiration || 
            option::spec_is_some(proposal.early_resolution_vote_threshold) && (post_proposal.yes_votes >= early_resolution_threshold ||
                                                                                post_proposal.no_votes >= early_resolution_threshold) && 
            post_proposal.yes_votes > post_proposal.no_votes && post_proposal.yes_votes + post_proposal.no_votes >= proposal.min_vote_threshold ==>
            simple_map::spec_contains_key(post_approved_hashes.hashes, proposal_id) && 
            simple_map::spec_get(post_approved_hashes.hashes, proposal_id) == execution_hash;*/
        ensures proposal_state_successed ==> simple_map::spec_contains_key(post_approved_hashes.hashes, proposal_id) && 
                                             simple_map::spec_get(post_approved_hashes.hashes, proposal_id) == execution_hash;
    }

    spec add_approved_script_hash(proposal_id: u64) {
        use aptos_framework::chain_status;
        // TODO: The variable `proposal_state` is the return value of the function `voting::get_proposal_state`.
        // The calling level of `voting::get_proposal_state` is very deep,
        // so the value of `proposal_state` cannot be obtained in the spec,
        // and the `aborts_if` of `proposal_state` cannot be written.
        // Can't cover all aborts_if conditions
        // pragma aborts_if_is_partial;

        requires chain_status::is_operating();
        /*
        aborts_if !exists<ApprovedExecutionHashes>(@aptos_framework);

        aborts_if !exists<voting::VotingForum<GovernanceProposal>>(@aptos_framework);
        let voting_forum = global<voting::VotingForum<GovernanceProposal>>(@aptos_framework);
        let proposal = table::spec_get(voting_forum.proposals, proposal_id);
        aborts_if !table::spec_contains(voting_forum.proposals, proposal_id);
        let early_resolution_threshold = option::spec_borrow(proposal.early_resolution_vote_threshold);
        aborts_if timestamp::now_seconds() <= proposal.expiration_secs && 
            (option::spec_is_none(proposal.early_resolution_vote_threshold) || 
            proposal.yes_votes < early_resolution_threshold && proposal.no_votes < early_resolution_threshold);
        aborts_if (timestamp::now_seconds() > proposal.expiration_secs || 
            option::spec_is_some(proposal.early_resolution_vote_threshold) && (proposal.yes_votes >= early_resolution_threshold || proposal.no_votes >= early_resolution_threshold)) &&
            (proposal.yes_votes <= proposal.no_votes || proposal.yes_votes + proposal.no_votes < proposal.min_vote_threshold);
        
        let post post_approved_hashes = global<ApprovedExecutionHashes>(@aptos_framework);
        ensures simple_map::spec_contains_key(post_approved_hashes.hashes, proposal_id) && 
            simple_map::spec_get(post_approved_hashes.hashes, proposal_id) == proposal.execution_hash;
        */
        
        include Schema_add_approved_script_hash;
    }

    spec add_approved_script_hash_script(proposal_id: u64) {
        // TODO: Calls `add_approved_script_hash`.
        // Can't cover all aborts_if conditions
        // pragma verify = false;
        use aptos_framework::chain_status;
        requires chain_status::is_operating();
        include Schema_add_approved_script_hash;
    }

    spec schema Schema_add_approved_script_hash {
        proposal_id: u64;
        
        aborts_if !exists<ApprovedExecutionHashes>(@aptos_framework);

        aborts_if !exists<voting::VotingForum<GovernanceProposal>>(@aptos_framework);
        let voting_forum = global<voting::VotingForum<GovernanceProposal>>(@aptos_framework);
        let proposal = table::spec_get(voting_forum.proposals, proposal_id);
        aborts_if !table::spec_contains(voting_forum.proposals, proposal_id);
        let early_resolution_threshold = option::spec_borrow(proposal.early_resolution_vote_threshold);
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
        // TODO: Executing the prove command gives an error that the target file is in `from_bcs::from_bytes`,
        // and the call level of the function `resolve` is too deep to obtain the parameter `bytes` of spec `from_bytes`,
        // so verification cannot be performed.
        // Can't cover all aborts_if conditions
        // pragma aborts_if_is_partial;

        requires chain_status::is_operating();

        /// verify voting::resolve
        include Voting_Is_proposal_resolvable_Abortsif;

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
        
        /// verify remove_approved_hash
        aborts_if !exists<ApprovedExecutionHashes>(@aptos_framework);
        let post post_approved_hashes = global<ApprovedExecutionHashes>(@aptos_framework).hashes;
        ensures !simple_map::spec_contains_key(post_approved_hashes, proposal_id);

        /// verify get_signer
        /* 
        aborts_if !exists<GovernanceResponsbility>(@aptos_framework);
        aborts_if !simple_map::spec_contains_key(governance_responsibility.signer_caps, signer_address);
        */
        include GetSignerAbortsIf;
        let governance_responsibility = global<GovernanceResponsbility>(@aptos_framework);
        let signer_cap = simple_map::spec_get(governance_responsibility.signer_caps, signer_address);
        let addr = signer_cap.account;
        ensures signer::address_of(result) == addr;
    }

    /// Address @aptos_framework must exist ApprovedExecutionHashes and GovernanceProposal.
    spec remove_approved_hash(proposal_id: u64) {
        aborts_if !exists<voting::VotingForum<GovernanceProposal>>(@aptos_framework);
        aborts_if !exists<ApprovedExecutionHashes>(@aptos_framework);
        let voting_forum = global<voting::VotingForum<GovernanceProposal>>(@aptos_framework);
        aborts_if !table::spec_contains(voting_forum.proposals, proposal_id);
        aborts_if !exists<voting::VotingForum<GovernanceProposal>>(@aptos_framework);
        let proposal = table::spec_get(voting_forum.proposals, proposal_id);
        aborts_if !proposal.is_resolved;
    }

    spec reconfigure(aptos_framework: &signer) {
        use aptos_framework::chain_status;
        use aptos_framework::coin::CoinInfo;
        use aptos_framework::aptos_coin::AptosCoin;
        use aptos_framework::transaction_fee;

        aborts_if !system_addresses::is_aptos_framework_address(signer::address_of(aptos_framework));

        include transaction_fee::RequiresCollectedFeesPerValueLeqBlockAptosSupply;
        requires chain_status::is_operating();
        requires timestamp::spec_now_microseconds() >= reconfiguration::last_reconfiguration_time();
        requires exists<stake::ValidatorFees>(@aptos_framework);
        requires exists<CoinInfo<AptosCoin>>(@aptos_framework);
    }

    /// Signer address must be @core_resources.
    /// signer must exist in MintCapStore.
    /// Address @aptos_framework must exist GovernanceResponsbility.
    spec get_signer_testnet_only(core_resources: &signer, signer_address: address): signer {
        aborts_if signer::address_of(core_resources) != @core_resources;
        aborts_if !exists<aptos_coin::MintCapStore>(signer::address_of(core_resources));
        include GetSignerAbortsIf;
    }

    /// Address @aptos_framework must exist StakingConfig.
    /// limit addition overflow.
    /// pool_address must exist in StakePool.
    spec get_voting_power(pool_address: address): u64 {
        // TODO: `stake::get_current_epoch_voting_power` is called in the function,
        // the call level is very deep, and `stake::get_stake` has multiple return values,
        // and multiple return values cannot be obtained in the spec,
        // so the overflow aborts_if of active + pending_active + pending_inactive cannot be written.
        // pragma aborts_if_is_partial;

        let staking_config = global<staking_config::StakingConfig>(@aptos_framework);
        aborts_if !exists<staking_config::StakingConfig>(@aptos_framework);
        let allow_validator_set_change = staking_config.allow_validator_set_change;
        let stake_pool = global<stake::StakePool>(pool_address);
        aborts_if allow_validator_set_change && (stake_pool.active.value + stake_pool.pending_active.value + stake_pool.pending_inactive.value) > MAX_U64;
        aborts_if !exists<stake::StakePool>(pool_address);
        aborts_if !allow_validator_set_change && !exists<stake::ValidatorSet>(@aptos_framework);
        aborts_if !allow_validator_set_change && stake::spec_is_current_epoch_validator(pool_address) && stake_pool.active.value + stake_pool.pending_inactive.value > MAX_U64;

        ensures allow_validator_set_change ==> result == stake_pool.active.value + stake_pool.pending_active.value + stake_pool.pending_inactive.value;
        ensures !allow_validator_set_change ==> if (stake::spec_is_current_epoch_validator(pool_address)) {
            result == stake_pool.active.value + stake_pool.pending_inactive.value
        } else {
            result == 0
        };
    }

    spec get_signer(signer_address: address): signer {
        include GetSignerAbortsIf;
    }

    spec schema GetSignerAbortsIf {
        signer_address: address;

        aborts_if !exists<GovernanceResponsbility>(@aptos_framework);
        let cap_map = global<GovernanceResponsbility>(@aptos_framework).signer_caps;
        aborts_if !simple_map::spec_contains_key(cap_map, signer_address);
    }

    spec create_proposal_metadata(metadata_location: vector<u8>, metadata_hash: vector<u8>): SimpleMap<String, vector<u8>> {
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

        // TODO: Executing the prove command gives an error that the target file is in `voting::is_proposal_resolvable`,
        // the level is too deep, it is difficult to obtain the value of `proposal_state`,
        // so it cannot be verified.
        // Can't cover all aborts_if conditions
        // pragma aborts_if_is_partial;
        // let voting_forum = borrow_global<voting::VotingForum<GovernanceProposal>>(@aptos_framework);
        // let proposal = table::spec_get(voting_forum.proposals, proposal_id);
        requires chain_status::is_operating();
        /*
        aborts_if !exists<voting::VotingForum<GovernanceProposal>>(@aptos_framework);
        aborts_if !exists<ApprovedExecutionHashes>(@aptos_framework);
        aborts_if !table::spec_contains(voting_forum.proposals,proposal_id);
        aborts_if !string::spec_internal_check_utf8(b"IS_MULTI_STEP_PROPOSAL_IN_EXECUTION");
        aborts_if aptos_framework::transaction_context::spec_get_script_hash() != proposal.execution_hash;
        include GetSignerAbortsIf;
        */
        
        /// verify voting::resolve_proposal_v2
        include Voting_Is_proposal_resolvable_Abortsif;

        let voting_forum = global<voting::VotingForum<GovernanceProposal>>(@aptos_framework);
        let proposal = table::spec_get(voting_forum.proposals, proposal_id);
        let post post_voting_forum = global<voting::VotingForum<GovernanceProposal>>(@aptos_framework);
        let post post_proposal = table::spec_get(voting_forum.proposals, proposal_id);

        aborts_if !string::spec_internal_check_utf8(voting::RESOLVABLE_TIME_METADATA_KEY);
        let multi_step_in_execution_key = utf8(voting::IS_MULTI_STEP_PROPOSAL_IN_EXECUTION_KEY);
        let post is_multi_step_proposal_in_execution_value = simple_map::spec_get(post_proposal.metadata, multi_step_in_execution_key);
        aborts_if simple_map::spec_contains_key(proposal.metadata, multi_step_in_execution_key) && !aptos_std::from_bcs::deserializable<vector<u8>>(b"true");
        /*ensures simple_map::spec_contains_key(proposal.metadata, multi_step_in_execution_key) ==>
            is_multi_step_proposal_in_execution_value == b"true";*/
        
        aborts_if !string::spec_internal_check_utf8(voting::IS_MULTI_STEP_PROPOSAL_KEY);
        let multi_step_key = utf8(voting::IS_MULTI_STEP_PROPOSAL_KEY);
        let is_multi_step = simple_map::spec_contains_key(proposal.metadata, multi_step_key) && 
                            aptos_std::from_bcs::deserialize<bool>(simple_map::spec_get(proposal.metadata, multi_step_key));
        let next_execution_hash_is_empty = len(next_execution_hash) == 0;
        aborts_if !is_multi_step || !next_execution_hash_is_empty;
        aborts_if next_execution_hash_is_empty && is_multi_step && !simple_map::spec_contains_key(proposal.metadata, multi_step_in_execution_key);
        ensures next_execution_hash_is_empty ==> post_proposal.is_resolved == true && post_proposal.resolution_time_secs == timestamp::now_seconds() && 
            if (is_multi_step) {
                is_multi_step_proposal_in_execution_value == b"false"
            } else {
                simple_map::spec_contains_key(proposal.metadata, multi_step_in_execution_key) ==>
                    is_multi_step_proposal_in_execution_value == b"true"
            };
        ensures !next_execution_hash_is_empty ==> post_proposal.execution_hash == next_execution_hash && 
            simple_map::spec_contains_key(proposal.metadata, multi_step_in_execution_key) ==>
                is_multi_step_proposal_in_execution_value == b"true";

        /// verify remove_approved_hash
        aborts_if next_execution_hash_is_empty && !exists<ApprovedExecutionHashes>(@aptos_framework);
        let post post_approved_hashes = global<ApprovedExecutionHashes>(@aptos_framework).hashes;
        ensures next_execution_hash_is_empty ==> !simple_map::spec_contains_key(post_approved_hashes, proposal_id);

        /// verify add_approved_script_hash
        aborts_if !next_execution_hash_is_empty && !exists<ApprovedExecutionHashes>(@aptos_framework);
        
        ensures !next_execution_hash_is_empty && 
            simple_map::spec_contains_key(post_approved_hashes, proposal_id) && 
            simple_map::spec_get(post_approved_hashes, proposal_id) == next_execution_hash;

        /// verify get_signer
        include GetSignerAbortsIf;
        let governance_responsibility = global<GovernanceResponsbility>(@aptos_framework);
        let signer_cap = simple_map::spec_get(governance_responsibility.signer_caps, signer_address);
        let addr = signer_cap.account;
        ensures signer::address_of(result) == addr;
    }

    spec schema Voting_Is_proposal_resolvable_Abortsif {
        proposal_id: u64;

        aborts_if !exists<voting::VotingForum<GovernanceProposal>>(@aptos_framework);
        let voting_forum = global<voting::VotingForum<GovernanceProposal>>(@aptos_framework);
        let proposal = table::spec_get(voting_forum.proposals, proposal_id);
        aborts_if !table::spec_contains(voting_forum.proposals, proposal_id);
        let early_resolution_threshold = option::spec_borrow(proposal.early_resolution_vote_threshold);
        aborts_if timestamp::now_seconds() <= proposal.expiration_secs && 
            (option::spec_is_none(proposal.early_resolution_vote_threshold) || 
            proposal.yes_votes < early_resolution_threshold && proposal.no_votes < early_resolution_threshold);
        aborts_if (timestamp::now_seconds() > proposal.expiration_secs || 
            option::spec_is_some(proposal.early_resolution_vote_threshold) && (proposal.yes_votes >= early_resolution_threshold || 
                                                                               proposal.no_votes >= early_resolution_threshold)) &&
            (proposal.yes_votes <= proposal.no_votes || proposal.yes_votes + proposal.no_votes < proposal.min_vote_threshold);
        aborts_if proposal.is_resolved;
        aborts_if !string::spec_internal_check_utf8(voting::RESOLVABLE_TIME_METADATA_KEY);
        aborts_if !simple_map::spec_contains_key(proposal.metadata, utf8(voting::RESOLVABLE_TIME_METADATA_KEY));
        let resolvable_time = aptos_std::from_bcs::deserialize<u64>(simple_map::spec_get(proposal.metadata, utf8(voting::RESOLVABLE_TIME_METADATA_KEY)));
        aborts_if !aptos_std::from_bcs::deserializable<u64>(simple_map::spec_get(proposal.metadata, utf8(voting::RESOLVABLE_TIME_METADATA_KEY)));
        aborts_if timestamp::now_seconds() <= resolvable_time;
        aborts_if aptos_framework::transaction_context::spec_get_script_hash() != proposal.execution_hash;
    }
}