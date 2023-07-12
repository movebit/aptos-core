spec aptos_framework::storage_gas {
    // -----------------
    // Struct invariants
    // -----------------

    spec Point {
        invariant x <= BASIS_POINT_DENOMINATION;
        invariant y <= BASIS_POINT_DENOMINATION;
    }

    spec GasCurve {
        invariant min_gas <= max_gas;
        invariant max_gas <= MAX_U64 / BASIS_POINT_DENOMINATION;

        invariant forall i in 0..len(points) - 1: (points[i].x < points[i + 1].x && points[i].y <= points[i + 1].y);
        invariant len(points) > 0 ==> points[0].x > 0;
        invariant len(points) > 0 ==> points[len(points) - 1].x < BASIS_POINT_DENOMINATION;
    }

    spec UsageGasConfig {
        invariant target_usage > 0;
        invariant target_usage <= MAX_U64 / BASIS_POINT_DENOMINATION;
    }


    // -----------------
    // Global invariants
    // -----------------

    spec module {
        use aptos_std::chain_status;
        pragma verify = true;
        pragma aborts_if_is_strict;
        // After genesis, `StateStorageUsage` and `GasParameter` exist.
        invariant [suspendable] chain_status::is_operating() ==> exists<StorageGasConfig>(@aptos_framework);
        invariant [suspendable] chain_status::is_operating() ==> exists<StorageGas>(@aptos_framework);
    }


    // -----------------------
    // Function specifications
    // -----------------------

    spec base_8192_exponential_curve(min_gas: u64, max_gas: u64): GasCurve {
        include NewGasCurveAbortsIf;

        ensures result.min_gas == min_gas;
        ensures result.max_gas == max_gas;
        ensures result.points[0].x == 1000 && result.points[0].y == 2
             && result.points[1].x == 2000 && result.points[1].y == 6
             && result.points[2].x == 3000 && result.points[2].y == 17
             && result.points[3].x == 4000 && result.points[3].y == 44
             && result.points[4].x == 5000 && result.points[4].y == 109
             && result.points[5].x == 6000 && result.points[5].y == 271
             && result.points[6].x == 7000 && result.points[6].y == 669
             && result.points[7].x == 8000 && result.points[7].y == 1648
             && result.points[8].x == 9000 && result.points[8].y == 4061
             && result.points[9].x == 9500 && result.points[9].y == 6372
             && result.points[10].x == 9900 && result.points[10].y == 9138;
    }

    spec new_point(x: u64, y: u64): Point {
        aborts_if x > BASIS_POINT_DENOMINATION || y > BASIS_POINT_DENOMINATION;

        ensures result.x == x;
        ensures result.y == y;
    }

    /// A non decreasing curve must ensure that next is greater than cur.
    spec new_gas_curve(min_gas: u64, max_gas: u64, points: vector<Point>): GasCurve {
        include NewGasCurveAbortsIf;
        include ValidatePointsAbortsIf;

        // property 3: The initialized gas curve structure has values set according to the provided parameters.
        ensures result.min_gas == min_gas;
        ensures result.max_gas == max_gas;
        ensures result.points == points;
    }

    spec new_usage_gas_config(target_usage: u64, read_curve: GasCurve, create_curve: GasCurve, write_curve: GasCurve): UsageGasConfig {
        aborts_if target_usage == 0;
        aborts_if target_usage > MAX_U64 / BASIS_POINT_DENOMINATION;

        // property 4: The initialized usage gas configuration structure has values set according to the provided parameters.
        ensures result.target_usage == target_usage
             && result.read_curve == read_curve
             && result.create_curve == create_curve
             && result.write_curve == write_curve;
    }

    spec new_storage_gas_config(item_config: UsageGasConfig, byte_config: UsageGasConfig): StorageGasConfig {
        aborts_if false;

        ensures result.item_config == item_config;
        ensures result.byte_config == byte_config;
    }

    /// Signer address must be @aptos_framework and StorageGasConfig exists.
    spec set_config(aptos_framework: &signer, config: StorageGasConfig) {
        include system_addresses::AbortsIfNotAptosFramework{ account: aptos_framework };
        aborts_if !exists<StorageGasConfig>(@aptos_framework);

        ensures global<StorageGasConfig>(@aptos_framework) == config;
    }

    /// Signer address must be @aptos_framework.
    /// Address @aptos_framework does not exist StorageGasConfig and StorageGas before the function call is restricted
    /// and exists after the function is executed.
    spec initialize(aptos_framework: &signer) {
        include system_addresses::AbortsIfNotAptosFramework{ account: aptos_framework };
        aborts_if exists<StorageGasConfig>(@aptos_framework);
        aborts_if exists<StorageGas>(@aptos_framework);

        // property 1: The module's initialization guarantees the creation of the StorageGasConfig resource with a precise configuration.
        ensures exists<StorageGasConfig>(@aptos_framework);
        ensures exists<StorageGas>(@aptos_framework);
    }

    /// A non decreasing curve must ensure that next is greater than cur.
    spec validate_points(points: &vector<Point>) {
        include ValidatePointsAbortsIf;

        ensures forall i in 0..len(points) - 1: points[i].x < points[i + 1].x && points[i].y <= points[i + 1].y;
        ensures len(points) > 0 ==> (points[0].x > 0 && points[len(points) - 1].x < BASIS_POINT_DENOMINATION);
    }

    spec calculate_gas(max_usage: u64, current_usage: u64, curve: &GasCurve): u64 {
        pragma opaque;
        // Not verified when verify_duration_estimate > vc_timeout
        pragma verify_duration_estimate = 120; // TODO: set because of timeout (property proved).
        requires max_usage > 0;
        requires max_usage <= MAX_U64 / BASIS_POINT_DENOMINATION;
        aborts_if false;
        ensures [abstract] result == spec_calculate_gas(max_usage, current_usage, curve);
    }

    spec interpolate(x0: u64, x1: u64, y0: u64, y1: u64, x: u64): u64 {
        pragma opaque;
        pragma intrinsic;

        aborts_if false;
    }

    /// Address @aptos_framework must exist StorageGasConfig and StorageGas and StateStorageUsage.
    spec on_reconfig {
        use aptos_std::chain_status;
        requires chain_status::is_operating();
        aborts_if !exists<StorageGasConfig>(@aptos_framework);
        aborts_if !exists<StorageGas>(@aptos_framework);
        aborts_if !exists<state_storage::StateStorageUsage>(@aptos_framework);

        let gas_config = global<StorageGasConfig>(@aptos_framework);
        let post gas = global<StorageGas>(@aptos_framework);
        let items = global<state_storage::StateStorageUsage>(@aptos_framework).usage.items;
        let bytes = global<state_storage::StateStorageUsage>(@aptos_framework).usage.bytes;
        ensures gas.per_item_read == spec_calculate_gas(gas_config.item_config.target_usage, items, gas_config.item_config.read_curve);
        ensures gas.per_item_create == spec_calculate_gas(gas_config.item_config.target_usage, items, gas_config.item_config.create_curve);
        ensures gas.per_item_write == spec_calculate_gas(gas_config.item_config.target_usage, items, gas_config.item_config.write_curve);
        ensures gas.per_byte_read == spec_calculate_gas(gas_config.byte_config.target_usage, bytes, gas_config.byte_config.read_curve);
        ensures gas.per_byte_create == spec_calculate_gas(gas_config.byte_config.target_usage, bytes, gas_config.byte_config.create_curve);
        ensures gas.per_byte_write == spec_calculate_gas(gas_config.byte_config.target_usage, bytes, gas_config.byte_config.write_curve);
    }


    // ---------------------------------
    // Spec helper functions and schemas
    // ---------------------------------

    spec fun spec_calculate_gas(max_usage: u64, current_usage: u64, curve: GasCurve): u64;

    spec schema NewGasCurveAbortsIf {
        min_gas: u64;
        max_gas: u64;

        aborts_if max_gas < min_gas;
        aborts_if max_gas > MAX_U64 / BASIS_POINT_DENOMINATION;
    }

    /// A non decreasing curve must ensure that next is greater than cur.
    spec schema ValidatePointsAbortsIf {
        points: vector<Point>;

        // preperty 2: The gas curve approximates an exponential curve based on a minimum and maximum gas charge.
        aborts_if exists i in 0..len(points) - 1: (
            points[i].x >= points[i + 1].x || points[i].y > points[i + 1].y
        );
        aborts_if len(points) > 0 && points[0].x == 0;
        aborts_if len(points) > 0 && points[len(points) - 1].x == BASIS_POINT_DENOMINATION;
    }
}
