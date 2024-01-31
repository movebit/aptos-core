spec 0x0::AnimeSwapPoolV1Library {

    spec module {
        pragma verify = true;
        pragma aborts_if_is_strict;
    }
    spec quote(amount_x: u64, reserve_x: u64, reserve_y: u64): u64{
        aborts_if amount_x <= 0 with ERR_INSUFFICIENT_AMOUNT;
        aborts_if (amount_x as u128) * (reserve_y as u128) > MAX_U128;
        aborts_if (reserve_x as u128) == 0;
    }
    spec get_amount_out(amount_in: u64, reserve_in: u64, reserve_out: u64, swap_fee: u64): u64{
        aborts_if amount_in <= 0 with ERR_INSUFFICIENT_INPUT_AMOUNT;
        let amount_in_with_fee = (amount_in as u128) * ((10000 - swap_fee) as u128);
        aborts_if 10000 - swap_fee < 0;
        aborts_if (amount_in as u128) * ((10000 - swap_fee) as u128) > MAX_U128;
        let numerator = amount_in_with_fee * (reserve_out as u128);
        aborts_if amount_in_with_fee * (reserve_out as u128) > MAX_U128;
        let denominator = (reserve_in as u128) * 10000 + amount_in_with_fee;
        aborts_if (reserve_in as u128) * 10000 > MAX_U128;
        aborts_if (reserve_in as u128) * 10000 + amount_in_with_fee > MAX_U128;
        aborts_if denominator == 0;
    }
    spec get_amount_in(amount_out: u64, reserve_in: u64, reserve_out: u64, swap_fee: u64): u64{
        aborts_if amount_out <= 0 with ERR_INSUFFICIENT_OUTPUT_AMOUNT;
        let numerator = (reserve_in as u128) * (amount_out as u128) * 10000;
        aborts_if (reserve_in as u128) * (amount_out as u128) > MAX_U128;
        aborts_if (reserve_in as u128) * (amount_out as u128) * 10000 > MAX_U128;
        let denominator = ((reserve_out - amount_out) as u128) * ((10000 - swap_fee) as u128);
        aborts_if reserve_out - amount_out < 0;
        aborts_if 10000 - swap_fee < 0;
        aborts_if ((reserve_out - amount_out) as u128) * ((10000 - swap_fee) as u128) > MAX_U128;
        aborts_if denominator == 0;
        aborts_if numerator / denominator + 1 > MAX_U128;
    }
    spec sqrt(x: u64, y: u64): u64{
    }
    spec sqrt_128(y: u128): u64{
    }
    spec min(x: u64, y: u64): u64{
    }
    spec overflow_add(a: u128, b: u128): u128{
        aborts_if MAX_U128 - b < 0;
        aborts_if MAX_U128 - a < 0;
        aborts_if a + b > MAX_U128;
    }
    spec is_overflow_mul(a: u128, b: u128): bool{
    }
    spec compare<CoinType1,CoinType2>(): bool{
        let type_name_coin_1 = type_info::type_name<CoinType1>();
        let type_name_coin_2 = type_info::type_name<CoinType2>();
        aborts_if type_name_coin_1 == type_name_coin_2 with ERR_COIN_TYPE_SAME_ERROR;
    }
    spec get_lpcoin_total_supply<LPCoin>(): u128{
    }
    spec register_coin<CoinType>(account: &signer){
    }
}

