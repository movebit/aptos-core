// Copyright © Aptos Foundation
// Parts of the project are originally copyright © Meta Platforms, Inc.
// SPDX-License-Identifier: Apache-2.0

use aptos_config::config::{
    EpochSnapshotPrunerConfig, LedgerPrunerConfig, PrunerConfig, StateMerklePrunerConfig,
};
use aptos_executor::block_executor::TransactionBlockExecutor;
use aptos_executor_benchmark::{
    benchmark_transaction::BenchmarkTransaction, native_executor::NativeExecutor,
    pipeline::PipelineConfig,
};
use aptos_metrics_core::{register_int_gauge, IntGauge};
use aptos_push_metrics::MetricsPusher;
use aptos_transaction_generator_lib::args::TransactionTypeArg;
use aptos_vm::AptosVM;
use clap::{Parser, Subcommand};
use once_cell::sync::Lazy;
use std::{
    path::PathBuf,
    time::{SystemTime, UNIX_EPOCH},
};

#[cfg(unix)]
#[global_allocator]
static ALLOC: jemallocator::Jemalloc = jemallocator::Jemalloc;

/// This is needed for filters on the Grafana dashboard working as its used to populate the filter
/// variables.
pub static START_TIME: Lazy<IntGauge> =
    Lazy::new(|| register_int_gauge!("node_process_start_time", "Start time").unwrap());

#[derive(Debug, Parser)]
struct PrunerOpt {
    #[clap(long)]
    enable_state_pruner: bool,

    #[clap(long)]
    enable_epoch_snapshot_pruner: bool,

    #[clap(long)]
    enable_ledger_pruner: bool,

    #[clap(long, default_value = "100000")]
    state_prune_window: u64,

    #[clap(long, default_value = "100000")]
    epoch_snapshot_prune_window: u64,

    #[clap(long, default_value = "100000")]
    ledger_prune_window: u64,

    #[clap(long, default_value = "500")]
    ledger_pruning_batch_size: usize,

    #[clap(long, default_value = "500")]
    state_pruning_batch_size: usize,

    #[clap(long, default_value = "500")]
    epoch_snapshot_pruning_batch_size: usize,
}

impl PrunerOpt {
    fn pruner_config(&self) -> PrunerConfig {
        PrunerConfig {
            state_merkle_pruner_config: StateMerklePrunerConfig {
                enable: self.enable_state_pruner,
                prune_window: self.state_prune_window,
                batch_size: self.state_pruning_batch_size,
            },
            epoch_snapshot_pruner_config: EpochSnapshotPrunerConfig {
                enable: self.enable_epoch_snapshot_pruner,
                prune_window: self.epoch_snapshot_prune_window,
                batch_size: self.epoch_snapshot_pruning_batch_size,
            },
            ledger_pruner_config: LedgerPrunerConfig {
                enable: self.enable_ledger_pruner,
                prune_window: self.ledger_prune_window,
                batch_size: self.ledger_pruning_batch_size,
                user_pruning_window_offset: 0,
            },
        }
    }
}

#[derive(Debug, Parser)]
pub struct PipelineOpt {
    #[clap(long)]
    split_stages: bool,
    #[clap(long)]
    allow_discards: bool,
    #[clap(long)]
    allow_aborts: bool,
}

impl PipelineOpt {
    fn pipeline_config(&self) -> PipelineConfig {
        PipelineConfig {
            split_stages: self.split_stages,
            allow_discards: self.allow_discards,
            allow_aborts: self.allow_aborts,
        }
    }
}

#[derive(Parser, Debug)]
struct Opt {
    #[clap(long, default_value = "10000")]
    block_size: usize,

    #[clap(long, default_value = "5")]
    transactions_per_sender: usize,

    #[clap(long, default_value = "1000000")]
    main_signer_accounts: usize,

    #[clap(long)]
    concurrency_level: Option<usize>,

    #[clap(flatten)]
    pruner_opt: PrunerOpt,

    #[clap(long)]
    use_state_kv_db: bool,

    #[clap(long)]
    use_sharded_state_merkle_db: bool,

    #[clap(flatten)]
    pipeline_opt: PipelineOpt,

    #[clap(subcommand)]
    cmd: Command,

    /// Verify sequence number of all the accounts after execution finishes
    #[clap(long)]
    verify_sequence_numbers: bool,

    #[clap(long)]
    use_native_executor: bool,
}

impl Opt {
    fn concurrency_level(&self) -> usize {
        match self.concurrency_level {
            None => {
                let level = num_cpus::get();
                println!(
                    "\nVM concurrency level defaults to num of cpus: {}\n",
                    level
                );
                level
            },
            Some(level) => level,
        }
    }
}

#[derive(Subcommand, Debug)]
enum Command {
    CreateDb {
        #[clap(long, parse(from_os_str))]
        data_dir: PathBuf,

        #[clap(long, default_value = "1000000")]
        num_accounts: usize,

        #[clap(long, default_value = "10000000000")]
        init_account_balance: u64,
    },
    RunExecutor {
        /// number of transfer blocks to run
        #[clap(long, default_value = "1000")]
        blocks: usize,

        /// Workload (transaction type). Uses raw coin transfer if not set,
        /// and if set uses transaction-generator-lib to generate it
        #[clap(long, arg_enum, ignore_case = true)]
        transaction_type: Option<TransactionTypeArg>,

        #[clap(long, parse(from_os_str))]
        data_dir: PathBuf,

        #[clap(long, parse(from_os_str))]
        checkpoint_dir: PathBuf,
    },
    AddAccounts {
        #[clap(long, parse(from_os_str))]
        data_dir: PathBuf,

        #[clap(long, parse(from_os_str))]
        checkpoint_dir: PathBuf,

        #[clap(long, default_value = "1000000")]
        num_new_accounts: usize,

        #[clap(long, default_value = "1000000")]
        init_account_balance: u64,
    },
}

fn run<E>(opt: Opt)
where
    E: TransactionBlockExecutor<BenchmarkTransaction> + 'static,
{
    match opt.cmd {
        Command::CreateDb {
            data_dir,
            num_accounts,
            init_account_balance,
        } => {
            aptos_executor_benchmark::db_generator::create_db_with_accounts::<E>(
                num_accounts,
                init_account_balance,
                opt.block_size,
                data_dir,
                opt.pruner_opt.pruner_config(),
                opt.verify_sequence_numbers,
                opt.use_state_kv_db,
                opt.use_sharded_state_merkle_db,
                opt.pipeline_opt.pipeline_config(),
            );
        },
        Command::RunExecutor {
            blocks,
            transaction_type,
            data_dir,
            checkpoint_dir,
        } => {
            aptos_executor_benchmark::run_benchmark::<E>(
                opt.block_size,
                blocks,
                transaction_type.map(|t| t.materialize()),
                opt.transactions_per_sender,
                opt.main_signer_accounts,
                data_dir,
                checkpoint_dir,
                opt.verify_sequence_numbers,
                opt.pruner_opt.pruner_config(),
                opt.use_state_kv_db,
                opt.use_sharded_state_merkle_db,
                opt.pipeline_opt.pipeline_config(),
            );
        },
        Command::AddAccounts {
            data_dir,
            checkpoint_dir,
            num_new_accounts,
            init_account_balance,
        } => {
            aptos_executor_benchmark::add_accounts::<E>(
                num_new_accounts,
                init_account_balance,
                opt.block_size,
                data_dir,
                checkpoint_dir,
                opt.pruner_opt.pruner_config(),
                opt.verify_sequence_numbers,
                opt.use_state_kv_db,
                opt.use_sharded_state_merkle_db,
                opt.pipeline_opt.pipeline_config(),
            );
        },
    }
}

fn main() {
    let opt = Opt::parse();
    aptos_logger::Logger::new().init();
    START_TIME.set(
        SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap()
            .as_millis() as i64,
    );
    let _mp = MetricsPusher::start_for_local_run("executor-benchmark");

    rayon::ThreadPoolBuilder::new()
        .thread_name(|index| format!("rayon-global-{}", index))
        .build_global()
        .expect("Failed to build rayon global thread pool.");
    AptosVM::set_concurrency_level_once(opt.concurrency_level());
    NativeExecutor::set_concurrency_level_once(opt.concurrency_level());

    if opt.use_native_executor {
        run::<NativeExecutor>(opt);
    } else {
        run::<AptosVM>(opt);
    }
}
