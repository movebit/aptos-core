
// ** Expanded prelude

// Copyright (c) The Diem Core Contributors
// Copyright (c) The Move Contributors
// SPDX-License-Identifier: Apache-2.0

// Basic theory for vectors using arrays. This version of vectors is not extensional.

type {:datatype} Vec _;

function {:constructor} Vec<T>(v: [int]T, l: int): Vec T;

function {:builtin "MapConst"} MapConstVec<T>(T): [int]T;
function DefaultVecElem<T>(): T;
function {:inline} DefaultVecMap<T>(): [int]T { MapConstVec(DefaultVecElem()) }

function {:inline} EmptyVec<T>(): Vec T {
    Vec(DefaultVecMap(), 0)
}

function {:inline} MakeVec1<T>(v: T): Vec T {
    Vec(DefaultVecMap()[0 := v], 1)
}

function {:inline} MakeVec2<T>(v1: T, v2: T): Vec T {
    Vec(DefaultVecMap()[0 := v1][1 := v2], 2)
}

function {:inline} MakeVec3<T>(v1: T, v2: T, v3: T): Vec T {
    Vec(DefaultVecMap()[0 := v1][1 := v2][2 := v3], 3)
}

function {:inline} MakeVec4<T>(v1: T, v2: T, v3: T, v4: T): Vec T {
    Vec(DefaultVecMap()[0 := v1][1 := v2][2 := v3][3 := v4], 4)
}

function {:inline} ExtendVec<T>(v: Vec T, elem: T): Vec T {
    (var l := l#Vec(v);
    Vec(v#Vec(v)[l := elem], l + 1))
}

function {:inline} ReadVec<T>(v: Vec T, i: int): T {
    v#Vec(v)[i]
}

function {:inline} LenVec<T>(v: Vec T): int {
    l#Vec(v)
}

function {:inline} IsEmptyVec<T>(v: Vec T): bool {
    l#Vec(v) == 0
}

function {:inline} RemoveVec<T>(v: Vec T): Vec T {
    (var l := l#Vec(v) - 1;
    Vec(v#Vec(v)[l := DefaultVecElem()], l))
}

function {:inline} RemoveAtVec<T>(v: Vec T, i: int): Vec T {
    (var l := l#Vec(v) - 1;
    Vec(
        (lambda j: int ::
           if j >= 0 && j < l then
               if j < i then v#Vec(v)[j] else v#Vec(v)[j+1]
           else DefaultVecElem()),
        l))
}

function {:inline} ConcatVec<T>(v1: Vec T, v2: Vec T): Vec T {
    (var l1, m1, l2, m2 := l#Vec(v1), v#Vec(v1), l#Vec(v2), v#Vec(v2);
    Vec(
        (lambda i: int ::
          if i >= 0 && i < l1 + l2 then
            if i < l1 then m1[i] else m2[i - l1]
          else DefaultVecElem()),
        l1 + l2))
}

function {:inline} ReverseVec<T>(v: Vec T): Vec T {
    (var l := l#Vec(v);
    Vec(
        (lambda i: int :: if 0 <= i && i < l then v#Vec(v)[l - i - 1] else DefaultVecElem()),
        l))
}

function {:inline} SliceVec<T>(v: Vec T, i: int, j: int): Vec T {
    (var m := v#Vec(v);
    Vec(
        (lambda k:int ::
          if 0 <= k && k < j - i then
            m[i + k]
          else
            DefaultVecElem()),
        (if j - i < 0 then 0 else j - i)))
}


function {:inline} UpdateVec<T>(v: Vec T, i: int, elem: T): Vec T {
    Vec(v#Vec(v)[i := elem], l#Vec(v))
}

function {:inline} SwapVec<T>(v: Vec T, i: int, j: int): Vec T {
    (var m := v#Vec(v);
    Vec(m[i := m[j]][j := m[i]], l#Vec(v)))
}

function {:inline} ContainsVec<T>(v: Vec T, e: T): bool {
    (var l := l#Vec(v);
    (exists i: int :: InRangeVec(v, i) && v#Vec(v)[i] == e))
}

function IndexOfVec<T>(v: Vec T, e: T): int;
axiom {:ctor "Vec"} (forall<T> v: Vec T, e: T :: {IndexOfVec(v, e)}
    (var i := IndexOfVec(v,e);
     if (!ContainsVec(v, e)) then i == -1
     else InRangeVec(v, i) && ReadVec(v, i) == e &&
        (forall j: int :: j >= 0 && j < i ==> ReadVec(v, j) != e)));

// This function should stay non-inlined as it guards many quantifiers
// over vectors. It appears important to have this uninterpreted for
// quantifier triggering.
function InRangeVec<T>(v: Vec T, i: int): bool {
    i >= 0 && i < LenVec(v)
}

// Copyright (c) The Diem Core Contributors
// Copyright (c) The Move Contributors
// SPDX-License-Identifier: Apache-2.0

// Boogie model for multisets, based on Boogie arrays. This theory assumes extensional equality for element types.

type {:datatype} Multiset _;
function {:constructor} Multiset<T>(v: [T]int, l: int): Multiset T;

function {:builtin "MapConst"} MapConstMultiset<T>(l: int): [T]int;

function {:inline} EmptyMultiset<T>(): Multiset T {
    Multiset(MapConstMultiset(0), 0)
}

function {:inline} LenMultiset<T>(s: Multiset T): int {
    l#Multiset(s)
}

function {:inline} ExtendMultiset<T>(s: Multiset T, v: T): Multiset T {
    (var len := l#Multiset(s);
    (var cnt := v#Multiset(s)[v];
    Multiset(v#Multiset(s)[v := (cnt + 1)], len + 1)))
}

// This function returns (s1 - s2). This function assumes that s2 is a subset of s1.
function {:inline} SubtractMultiset<T>(s1: Multiset T, s2: Multiset T): Multiset T {
    (var len1 := l#Multiset(s1);
    (var len2 := l#Multiset(s2);
    Multiset((lambda v:T :: v#Multiset(s1)[v]-v#Multiset(s2)[v]), len1-len2)))
}

function {:inline} IsEmptyMultiset<T>(s: Multiset T): bool {
    (l#Multiset(s) == 0) &&
    (forall v: T :: v#Multiset(s)[v] == 0)
}

function {:inline} IsSubsetMultiset<T>(s1: Multiset T, s2: Multiset T): bool {
    (l#Multiset(s1) <= l#Multiset(s2)) &&
    (forall v: T :: v#Multiset(s1)[v] <= v#Multiset(s2)[v])
}

function {:inline} ContainsMultiset<T>(s: Multiset T, v: T): bool {
    v#Multiset(s)[v] > 0
}

// Copyright (c) The Diem Core Contributors
// Copyright (c) The Move Contributors
// SPDX-License-Identifier: Apache-2.0

// Theory for tables.

type {:datatype} Table _ _;

// v is the SMT array holding the key-value assignment. e is an array which
// independently determines whether a key is valid or not. l is the length.
//
// Note that even though the program cannot reflect over existence of a key,
// we want the specification to be able to do this, so it can express
// verification conditions like "key has been inserted".
function {:constructor} Table<K, V>(v: [K]V, e: [K]bool, l: int): Table K V;

// Functions for default SMT arrays. For the table values, we don't care and
// use an uninterpreted function.
function DefaultTableArray<K, V>(): [K]V;
function DefaultTableKeyExistsArray<K>(): [K]bool;
axiom DefaultTableKeyExistsArray() == (lambda i: int :: false);

function {:inline} EmptyTable<K, V>(): Table K V {
    Table(DefaultTableArray(), DefaultTableKeyExistsArray(), 0)
}

function {:inline} GetTable<K,V>(t: Table K V, k: K): V {
    // Notice we do not check whether key is in the table. The result is undetermined if it is not.
    v#Table(t)[k]
}

function {:inline} LenTable<K,V>(t: Table K V): int {
    l#Table(t)
}


function {:inline} ContainsTable<K,V>(t: Table K V, k: K): bool {
    e#Table(t)[k]
}

function {:inline} UpdateTable<K,V>(t: Table K V, k: K, v: V): Table K V {
    Table(v#Table(t)[k := v], e#Table(t), l#Table(t))
}

function {:inline} AddTable<K,V>(t: Table K V, k: K, v: V): Table K V {
    // This function has an undetermined result if the key is already in the table
    // (all specification functions have this "partial definiteness" behavior). Thus we can
    // just increment the length.
    Table(v#Table(t)[k := v], e#Table(t)[k := true], l#Table(t) + 1)
}

function {:inline} RemoveTable<K,V>(t: Table K V, k: K): Table K V {
    // Similar as above, we only need to consider the case where the key is in the table.
    Table(v#Table(t), e#Table(t)[k := false], l#Table(t) - 1)
}

axiom {:ctor "Table"} (forall<K,V> t: Table K V :: {LenTable(t)}
    (exists k: K :: {ContainsTable(t, k)} ContainsTable(t, k)) ==> LenTable(t) >= 1
);
// TODO: we might want to encoder a stronger property that the length of table
// must be more than N given a set of N items. Currently we don't see a need here
// and the above axiom seems to be sufficient.
// Copyright © Aptos Foundation
// SPDX-License-Identifier: Apache-2.0

// ==================================================================================
// Native object::exists_at

// ==================================================================================
// Intrinsic implementation of aggregator and aggregator factory

type {:datatype} $1_aggregator_Aggregator;
function {:constructor} $1_aggregator_Aggregator($handle: int, $key: int, $limit: int, $val: int): $1_aggregator_Aggregator;
function {:inline} $Update'$1_aggregator_Aggregator'_handle(s: $1_aggregator_Aggregator, x: int): $1_aggregator_Aggregator {
    $1_aggregator_Aggregator(x, $key#$1_aggregator_Aggregator(s), $limit#$1_aggregator_Aggregator(s), $val#$1_aggregator_Aggregator(s))
}
function {:inline} $Update'$1_aggregator_Aggregator'_key(s: $1_aggregator_Aggregator, x: int): $1_aggregator_Aggregator {
    $1_aggregator_Aggregator($handle#$1_aggregator_Aggregator(s), x, $limit#$1_aggregator_Aggregator(s), $val#$1_aggregator_Aggregator(s))
}
function {:inline} $Update'$1_aggregator_Aggregator'_limit(s: $1_aggregator_Aggregator, x: int): $1_aggregator_Aggregator {
    $1_aggregator_Aggregator($handle#$1_aggregator_Aggregator(s), $key#$1_aggregator_Aggregator(s), x, $val#$1_aggregator_Aggregator(s))
}
function {:inline} $Update'$1_aggregator_Aggregator'_val(s: $1_aggregator_Aggregator, x: int): $1_aggregator_Aggregator {
    $1_aggregator_Aggregator($handle#$1_aggregator_Aggregator(s), $key#$1_aggregator_Aggregator(s), $limit#$1_aggregator_Aggregator(s), x)
}
function $IsValid'$1_aggregator_Aggregator'(s: $1_aggregator_Aggregator): bool {
    $IsValid'address'($handle#$1_aggregator_Aggregator(s))
      && $IsValid'address'($key#$1_aggregator_Aggregator(s))
      && $IsValid'u128'($limit#$1_aggregator_Aggregator(s))
      && $IsValid'u128'($val#$1_aggregator_Aggregator(s))
}
function {:inline} $IsEqual'$1_aggregator_Aggregator'(s1: $1_aggregator_Aggregator, s2: $1_aggregator_Aggregator): bool {
    s1 == s2
}
function {:inline} $1_aggregator_spec_get_limit(s1: $1_aggregator_Aggregator): int {
    $limit#$1_aggregator_Aggregator(s1)
}
function {:inline} $1_aggregator_spec_get_handle(s1: $1_aggregator_Aggregator): int {
    $handle#$1_aggregator_Aggregator(s1)
}
function {:inline} $1_aggregator_spec_get_key(s1: $1_aggregator_Aggregator): int {
    $key#$1_aggregator_Aggregator(s1)
}
function {:inline} $1_aggregator_spec_get_val(s1: $1_aggregator_Aggregator): int {
    $val#$1_aggregator_Aggregator(s1)
}

function $1_aggregator_spec_read(agg: $1_aggregator_Aggregator): int {
    $1_aggregator_spec_get_val(agg)
}

function $1_aggregator_spec_aggregator_set_val(agg: $1_aggregator_Aggregator, val: int): $1_aggregator_Aggregator {
    $Update'$1_aggregator_Aggregator'_val(agg, val)
}

function $1_aggregator_spec_aggregator_get_val(agg: $1_aggregator_Aggregator): int {
    $1_aggregator_spec_get_val(agg)
}

function $1_aggregator_factory_spec_new_aggregator(limit: int) : $1_aggregator_Aggregator;

axiom (forall limit: int :: {$1_aggregator_factory_spec_new_aggregator(limit)}
    (var agg := $1_aggregator_factory_spec_new_aggregator(limit);
     $1_aggregator_spec_get_limit(agg) == limit));

axiom (forall limit: int :: {$1_aggregator_factory_spec_new_aggregator(limit)}
     (var agg := $1_aggregator_factory_spec_new_aggregator(limit);
     $1_aggregator_spec_aggregator_get_val(agg) == 0));


// ============================================================================================
// Primitive Types

const $MAX_U8: int;
axiom $MAX_U8 == 255;
const $MAX_U16: int;
axiom $MAX_U16 == 65535;
const $MAX_U32: int;
axiom $MAX_U32 == 4294967295;
const $MAX_U64: int;
axiom $MAX_U64 == 18446744073709551615;
const $MAX_U128: int;
axiom $MAX_U128 == 340282366920938463463374607431768211455;
const $MAX_U256: int;
axiom $MAX_U256 == 115792089237316195423570985008687907853269984665640564039457584007913129639935;

// Templates for bitvector operations

function {:bvbuiltin "bvand"} $And'Bv8'(bv8,bv8) returns(bv8);
function {:bvbuiltin "bvor"} $Or'Bv8'(bv8,bv8) returns(bv8);
function {:bvbuiltin "bvxor"} $Xor'Bv8'(bv8,bv8) returns(bv8);
function {:bvbuiltin "bvadd"} $Add'Bv8'(bv8,bv8) returns(bv8);
function {:bvbuiltin "bvsub"} $Sub'Bv8'(bv8,bv8) returns(bv8);
function {:bvbuiltin "bvmul"} $Mul'Bv8'(bv8,bv8) returns(bv8);
function {:bvbuiltin "bvudiv"} $Div'Bv8'(bv8,bv8) returns(bv8);
function {:bvbuiltin "bvurem"} $Mod'Bv8'(bv8,bv8) returns(bv8);
function {:bvbuiltin "bvshl"} $Shl'Bv8'(bv8,bv8) returns(bv8);
function {:bvbuiltin "bvlshr"} $Shr'Bv8'(bv8,bv8) returns(bv8);
function {:bvbuiltin "bvult"} $Lt'Bv8'(bv8,bv8) returns(bool);
function {:bvbuiltin "bvule"} $Le'Bv8'(bv8,bv8) returns(bool);
function {:bvbuiltin "bvugt"} $Gt'Bv8'(bv8,bv8) returns(bool);
function {:bvbuiltin "bvuge"} $Ge'Bv8'(bv8,bv8) returns(bool);

procedure {:inline 1} $AddBv8(src1: bv8, src2: bv8) returns (dst: bv8)
{
    if ($Lt'Bv8'($Add'Bv8'(src1, src2), src1)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Add'Bv8'(src1, src2);
}

procedure {:inline 1} $AddBv8_unchecked(src1: bv8, src2: bv8) returns (dst: bv8)
{
    dst := $Add'Bv8'(src1, src2);
}

procedure {:inline 1} $SubBv8(src1: bv8, src2: bv8) returns (dst: bv8)
{
    if ($Lt'Bv8'(src1, src2)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Sub'Bv8'(src1, src2);
}

procedure {:inline 1} $MulBv8(src1: bv8, src2: bv8) returns (dst: bv8)
{
    if ($Lt'Bv8'($Mul'Bv8'(src1, src2), src1)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Mul'Bv8'(src1, src2);
}

procedure {:inline 1} $DivBv8(src1: bv8, src2: bv8) returns (dst: bv8)
{
    if (src2 == 0bv8) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Div'Bv8'(src1, src2);
}

procedure {:inline 1} $ModBv8(src1: bv8, src2: bv8) returns (dst: bv8)
{
    if (src2 == 0bv8) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Mod'Bv8'(src1, src2);
}

procedure {:inline 1} $AndBv8(src1: bv8, src2: bv8) returns (dst: bv8)
{
    dst := $And'Bv8'(src1,src2);
}

procedure {:inline 1} $OrBv8(src1: bv8, src2: bv8) returns (dst: bv8)
{
    dst := $Or'Bv8'(src1,src2);
}

procedure {:inline 1} $XorBv8(src1: bv8, src2: bv8) returns (dst: bv8)
{
    dst := $Xor'Bv8'(src1,src2);
}

procedure {:inline 1} $LtBv8(src1: bv8, src2: bv8) returns (dst: bool)
{
    dst := $Lt'Bv8'(src1,src2);
}

procedure {:inline 1} $LeBv8(src1: bv8, src2: bv8) returns (dst: bool)
{
    dst := $Le'Bv8'(src1,src2);
}

procedure {:inline 1} $GtBv8(src1: bv8, src2: bv8) returns (dst: bool)
{
    dst := $Gt'Bv8'(src1,src2);
}

procedure {:inline 1} $GeBv8(src1: bv8, src2: bv8) returns (dst: bool)
{
    dst := $Ge'Bv8'(src1,src2);
}

function $IsValid'bv8'(v: bv8): bool {
  $Ge'Bv8'(v,0bv8) && $Le'Bv8'(v,255bv8)
}

function {:inline} $IsEqual'bv8'(x: bv8, y: bv8): bool {
    x == y
}

procedure {:inline 1} $int2bv8(src: int) returns (dst: bv8)
{
    if (src > 255) {
        call $ExecFailureAbort();
        return;
    }
    dst := $int2bv.8(src);
}

procedure {:inline 1} $bv2int8(src: bv8) returns (dst: int)
{
    dst := $bv2int.8(src);
}

function {:builtin "(_ int2bv 8)"} $int2bv.8(i: int) returns (bv8);
function {:builtin "bv2nat"} $bv2int.8(i: bv8) returns (int);

function {:bvbuiltin "bvand"} $And'Bv16'(bv16,bv16) returns(bv16);
function {:bvbuiltin "bvor"} $Or'Bv16'(bv16,bv16) returns(bv16);
function {:bvbuiltin "bvxor"} $Xor'Bv16'(bv16,bv16) returns(bv16);
function {:bvbuiltin "bvadd"} $Add'Bv16'(bv16,bv16) returns(bv16);
function {:bvbuiltin "bvsub"} $Sub'Bv16'(bv16,bv16) returns(bv16);
function {:bvbuiltin "bvmul"} $Mul'Bv16'(bv16,bv16) returns(bv16);
function {:bvbuiltin "bvudiv"} $Div'Bv16'(bv16,bv16) returns(bv16);
function {:bvbuiltin "bvurem"} $Mod'Bv16'(bv16,bv16) returns(bv16);
function {:bvbuiltin "bvshl"} $Shl'Bv16'(bv16,bv16) returns(bv16);
function {:bvbuiltin "bvlshr"} $Shr'Bv16'(bv16,bv16) returns(bv16);
function {:bvbuiltin "bvult"} $Lt'Bv16'(bv16,bv16) returns(bool);
function {:bvbuiltin "bvule"} $Le'Bv16'(bv16,bv16) returns(bool);
function {:bvbuiltin "bvugt"} $Gt'Bv16'(bv16,bv16) returns(bool);
function {:bvbuiltin "bvuge"} $Ge'Bv16'(bv16,bv16) returns(bool);

procedure {:inline 1} $AddBv16(src1: bv16, src2: bv16) returns (dst: bv16)
{
    if ($Lt'Bv16'($Add'Bv16'(src1, src2), src1)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Add'Bv16'(src1, src2);
}

procedure {:inline 1} $AddBv16_unchecked(src1: bv16, src2: bv16) returns (dst: bv16)
{
    dst := $Add'Bv16'(src1, src2);
}

procedure {:inline 1} $SubBv16(src1: bv16, src2: bv16) returns (dst: bv16)
{
    if ($Lt'Bv16'(src1, src2)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Sub'Bv16'(src1, src2);
}

procedure {:inline 1} $MulBv16(src1: bv16, src2: bv16) returns (dst: bv16)
{
    if ($Lt'Bv16'($Mul'Bv16'(src1, src2), src1)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Mul'Bv16'(src1, src2);
}

procedure {:inline 1} $DivBv16(src1: bv16, src2: bv16) returns (dst: bv16)
{
    if (src2 == 0bv16) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Div'Bv16'(src1, src2);
}

procedure {:inline 1} $ModBv16(src1: bv16, src2: bv16) returns (dst: bv16)
{
    if (src2 == 0bv16) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Mod'Bv16'(src1, src2);
}

procedure {:inline 1} $AndBv16(src1: bv16, src2: bv16) returns (dst: bv16)
{
    dst := $And'Bv16'(src1,src2);
}

procedure {:inline 1} $OrBv16(src1: bv16, src2: bv16) returns (dst: bv16)
{
    dst := $Or'Bv16'(src1,src2);
}

procedure {:inline 1} $XorBv16(src1: bv16, src2: bv16) returns (dst: bv16)
{
    dst := $Xor'Bv16'(src1,src2);
}

procedure {:inline 1} $LtBv16(src1: bv16, src2: bv16) returns (dst: bool)
{
    dst := $Lt'Bv16'(src1,src2);
}

procedure {:inline 1} $LeBv16(src1: bv16, src2: bv16) returns (dst: bool)
{
    dst := $Le'Bv16'(src1,src2);
}

procedure {:inline 1} $GtBv16(src1: bv16, src2: bv16) returns (dst: bool)
{
    dst := $Gt'Bv16'(src1,src2);
}

procedure {:inline 1} $GeBv16(src1: bv16, src2: bv16) returns (dst: bool)
{
    dst := $Ge'Bv16'(src1,src2);
}

function $IsValid'bv16'(v: bv16): bool {
  $Ge'Bv16'(v,0bv16) && $Le'Bv16'(v,65535bv16)
}

function {:inline} $IsEqual'bv16'(x: bv16, y: bv16): bool {
    x == y
}

procedure {:inline 1} $int2bv16(src: int) returns (dst: bv16)
{
    if (src > 65535) {
        call $ExecFailureAbort();
        return;
    }
    dst := $int2bv.16(src);
}

procedure {:inline 1} $bv2int16(src: bv16) returns (dst: int)
{
    dst := $bv2int.16(src);
}

function {:builtin "(_ int2bv 16)"} $int2bv.16(i: int) returns (bv16);
function {:builtin "bv2nat"} $bv2int.16(i: bv16) returns (int);

function {:bvbuiltin "bvand"} $And'Bv32'(bv32,bv32) returns(bv32);
function {:bvbuiltin "bvor"} $Or'Bv32'(bv32,bv32) returns(bv32);
function {:bvbuiltin "bvxor"} $Xor'Bv32'(bv32,bv32) returns(bv32);
function {:bvbuiltin "bvadd"} $Add'Bv32'(bv32,bv32) returns(bv32);
function {:bvbuiltin "bvsub"} $Sub'Bv32'(bv32,bv32) returns(bv32);
function {:bvbuiltin "bvmul"} $Mul'Bv32'(bv32,bv32) returns(bv32);
function {:bvbuiltin "bvudiv"} $Div'Bv32'(bv32,bv32) returns(bv32);
function {:bvbuiltin "bvurem"} $Mod'Bv32'(bv32,bv32) returns(bv32);
function {:bvbuiltin "bvshl"} $Shl'Bv32'(bv32,bv32) returns(bv32);
function {:bvbuiltin "bvlshr"} $Shr'Bv32'(bv32,bv32) returns(bv32);
function {:bvbuiltin "bvult"} $Lt'Bv32'(bv32,bv32) returns(bool);
function {:bvbuiltin "bvule"} $Le'Bv32'(bv32,bv32) returns(bool);
function {:bvbuiltin "bvugt"} $Gt'Bv32'(bv32,bv32) returns(bool);
function {:bvbuiltin "bvuge"} $Ge'Bv32'(bv32,bv32) returns(bool);

procedure {:inline 1} $AddBv32(src1: bv32, src2: bv32) returns (dst: bv32)
{
    if ($Lt'Bv32'($Add'Bv32'(src1, src2), src1)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Add'Bv32'(src1, src2);
}

procedure {:inline 1} $AddBv32_unchecked(src1: bv32, src2: bv32) returns (dst: bv32)
{
    dst := $Add'Bv32'(src1, src2);
}

procedure {:inline 1} $SubBv32(src1: bv32, src2: bv32) returns (dst: bv32)
{
    if ($Lt'Bv32'(src1, src2)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Sub'Bv32'(src1, src2);
}

procedure {:inline 1} $MulBv32(src1: bv32, src2: bv32) returns (dst: bv32)
{
    if ($Lt'Bv32'($Mul'Bv32'(src1, src2), src1)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Mul'Bv32'(src1, src2);
}

procedure {:inline 1} $DivBv32(src1: bv32, src2: bv32) returns (dst: bv32)
{
    if (src2 == 0bv32) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Div'Bv32'(src1, src2);
}

procedure {:inline 1} $ModBv32(src1: bv32, src2: bv32) returns (dst: bv32)
{
    if (src2 == 0bv32) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Mod'Bv32'(src1, src2);
}

procedure {:inline 1} $AndBv32(src1: bv32, src2: bv32) returns (dst: bv32)
{
    dst := $And'Bv32'(src1,src2);
}

procedure {:inline 1} $OrBv32(src1: bv32, src2: bv32) returns (dst: bv32)
{
    dst := $Or'Bv32'(src1,src2);
}

procedure {:inline 1} $XorBv32(src1: bv32, src2: bv32) returns (dst: bv32)
{
    dst := $Xor'Bv32'(src1,src2);
}

procedure {:inline 1} $LtBv32(src1: bv32, src2: bv32) returns (dst: bool)
{
    dst := $Lt'Bv32'(src1,src2);
}

procedure {:inline 1} $LeBv32(src1: bv32, src2: bv32) returns (dst: bool)
{
    dst := $Le'Bv32'(src1,src2);
}

procedure {:inline 1} $GtBv32(src1: bv32, src2: bv32) returns (dst: bool)
{
    dst := $Gt'Bv32'(src1,src2);
}

procedure {:inline 1} $GeBv32(src1: bv32, src2: bv32) returns (dst: bool)
{
    dst := $Ge'Bv32'(src1,src2);
}

function $IsValid'bv32'(v: bv32): bool {
  $Ge'Bv32'(v,0bv32) && $Le'Bv32'(v,2147483647bv32)
}

function {:inline} $IsEqual'bv32'(x: bv32, y: bv32): bool {
    x == y
}

procedure {:inline 1} $int2bv32(src: int) returns (dst: bv32)
{
    if (src > 2147483647) {
        call $ExecFailureAbort();
        return;
    }
    dst := $int2bv.32(src);
}

procedure {:inline 1} $bv2int32(src: bv32) returns (dst: int)
{
    dst := $bv2int.32(src);
}

function {:builtin "(_ int2bv 32)"} $int2bv.32(i: int) returns (bv32);
function {:builtin "bv2nat"} $bv2int.32(i: bv32) returns (int);

function {:bvbuiltin "bvand"} $And'Bv64'(bv64,bv64) returns(bv64);
function {:bvbuiltin "bvor"} $Or'Bv64'(bv64,bv64) returns(bv64);
function {:bvbuiltin "bvxor"} $Xor'Bv64'(bv64,bv64) returns(bv64);
function {:bvbuiltin "bvadd"} $Add'Bv64'(bv64,bv64) returns(bv64);
function {:bvbuiltin "bvsub"} $Sub'Bv64'(bv64,bv64) returns(bv64);
function {:bvbuiltin "bvmul"} $Mul'Bv64'(bv64,bv64) returns(bv64);
function {:bvbuiltin "bvudiv"} $Div'Bv64'(bv64,bv64) returns(bv64);
function {:bvbuiltin "bvurem"} $Mod'Bv64'(bv64,bv64) returns(bv64);
function {:bvbuiltin "bvshl"} $Shl'Bv64'(bv64,bv64) returns(bv64);
function {:bvbuiltin "bvlshr"} $Shr'Bv64'(bv64,bv64) returns(bv64);
function {:bvbuiltin "bvult"} $Lt'Bv64'(bv64,bv64) returns(bool);
function {:bvbuiltin "bvule"} $Le'Bv64'(bv64,bv64) returns(bool);
function {:bvbuiltin "bvugt"} $Gt'Bv64'(bv64,bv64) returns(bool);
function {:bvbuiltin "bvuge"} $Ge'Bv64'(bv64,bv64) returns(bool);

procedure {:inline 1} $AddBv64(src1: bv64, src2: bv64) returns (dst: bv64)
{
    if ($Lt'Bv64'($Add'Bv64'(src1, src2), src1)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Add'Bv64'(src1, src2);
}

procedure {:inline 1} $AddBv64_unchecked(src1: bv64, src2: bv64) returns (dst: bv64)
{
    dst := $Add'Bv64'(src1, src2);
}

procedure {:inline 1} $SubBv64(src1: bv64, src2: bv64) returns (dst: bv64)
{
    if ($Lt'Bv64'(src1, src2)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Sub'Bv64'(src1, src2);
}

procedure {:inline 1} $MulBv64(src1: bv64, src2: bv64) returns (dst: bv64)
{
    if ($Lt'Bv64'($Mul'Bv64'(src1, src2), src1)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Mul'Bv64'(src1, src2);
}

procedure {:inline 1} $DivBv64(src1: bv64, src2: bv64) returns (dst: bv64)
{
    if (src2 == 0bv64) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Div'Bv64'(src1, src2);
}

procedure {:inline 1} $ModBv64(src1: bv64, src2: bv64) returns (dst: bv64)
{
    if (src2 == 0bv64) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Mod'Bv64'(src1, src2);
}

procedure {:inline 1} $AndBv64(src1: bv64, src2: bv64) returns (dst: bv64)
{
    dst := $And'Bv64'(src1,src2);
}

procedure {:inline 1} $OrBv64(src1: bv64, src2: bv64) returns (dst: bv64)
{
    dst := $Or'Bv64'(src1,src2);
}

procedure {:inline 1} $XorBv64(src1: bv64, src2: bv64) returns (dst: bv64)
{
    dst := $Xor'Bv64'(src1,src2);
}

procedure {:inline 1} $LtBv64(src1: bv64, src2: bv64) returns (dst: bool)
{
    dst := $Lt'Bv64'(src1,src2);
}

procedure {:inline 1} $LeBv64(src1: bv64, src2: bv64) returns (dst: bool)
{
    dst := $Le'Bv64'(src1,src2);
}

procedure {:inline 1} $GtBv64(src1: bv64, src2: bv64) returns (dst: bool)
{
    dst := $Gt'Bv64'(src1,src2);
}

procedure {:inline 1} $GeBv64(src1: bv64, src2: bv64) returns (dst: bool)
{
    dst := $Ge'Bv64'(src1,src2);
}

function $IsValid'bv64'(v: bv64): bool {
  $Ge'Bv64'(v,0bv64) && $Le'Bv64'(v,18446744073709551615bv64)
}

function {:inline} $IsEqual'bv64'(x: bv64, y: bv64): bool {
    x == y
}

procedure {:inline 1} $int2bv64(src: int) returns (dst: bv64)
{
    if (src > 18446744073709551615) {
        call $ExecFailureAbort();
        return;
    }
    dst := $int2bv.64(src);
}

procedure {:inline 1} $bv2int64(src: bv64) returns (dst: int)
{
    dst := $bv2int.64(src);
}

function {:builtin "(_ int2bv 64)"} $int2bv.64(i: int) returns (bv64);
function {:builtin "bv2nat"} $bv2int.64(i: bv64) returns (int);

function {:bvbuiltin "bvand"} $And'Bv128'(bv128,bv128) returns(bv128);
function {:bvbuiltin "bvor"} $Or'Bv128'(bv128,bv128) returns(bv128);
function {:bvbuiltin "bvxor"} $Xor'Bv128'(bv128,bv128) returns(bv128);
function {:bvbuiltin "bvadd"} $Add'Bv128'(bv128,bv128) returns(bv128);
function {:bvbuiltin "bvsub"} $Sub'Bv128'(bv128,bv128) returns(bv128);
function {:bvbuiltin "bvmul"} $Mul'Bv128'(bv128,bv128) returns(bv128);
function {:bvbuiltin "bvudiv"} $Div'Bv128'(bv128,bv128) returns(bv128);
function {:bvbuiltin "bvurem"} $Mod'Bv128'(bv128,bv128) returns(bv128);
function {:bvbuiltin "bvshl"} $Shl'Bv128'(bv128,bv128) returns(bv128);
function {:bvbuiltin "bvlshr"} $Shr'Bv128'(bv128,bv128) returns(bv128);
function {:bvbuiltin "bvult"} $Lt'Bv128'(bv128,bv128) returns(bool);
function {:bvbuiltin "bvule"} $Le'Bv128'(bv128,bv128) returns(bool);
function {:bvbuiltin "bvugt"} $Gt'Bv128'(bv128,bv128) returns(bool);
function {:bvbuiltin "bvuge"} $Ge'Bv128'(bv128,bv128) returns(bool);

procedure {:inline 1} $AddBv128(src1: bv128, src2: bv128) returns (dst: bv128)
{
    if ($Lt'Bv128'($Add'Bv128'(src1, src2), src1)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Add'Bv128'(src1, src2);
}

procedure {:inline 1} $AddBv128_unchecked(src1: bv128, src2: bv128) returns (dst: bv128)
{
    dst := $Add'Bv128'(src1, src2);
}

procedure {:inline 1} $SubBv128(src1: bv128, src2: bv128) returns (dst: bv128)
{
    if ($Lt'Bv128'(src1, src2)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Sub'Bv128'(src1, src2);
}

procedure {:inline 1} $MulBv128(src1: bv128, src2: bv128) returns (dst: bv128)
{
    if ($Lt'Bv128'($Mul'Bv128'(src1, src2), src1)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Mul'Bv128'(src1, src2);
}

procedure {:inline 1} $DivBv128(src1: bv128, src2: bv128) returns (dst: bv128)
{
    if (src2 == 0bv128) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Div'Bv128'(src1, src2);
}

procedure {:inline 1} $ModBv128(src1: bv128, src2: bv128) returns (dst: bv128)
{
    if (src2 == 0bv128) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Mod'Bv128'(src1, src2);
}

procedure {:inline 1} $AndBv128(src1: bv128, src2: bv128) returns (dst: bv128)
{
    dst := $And'Bv128'(src1,src2);
}

procedure {:inline 1} $OrBv128(src1: bv128, src2: bv128) returns (dst: bv128)
{
    dst := $Or'Bv128'(src1,src2);
}

procedure {:inline 1} $XorBv128(src1: bv128, src2: bv128) returns (dst: bv128)
{
    dst := $Xor'Bv128'(src1,src2);
}

procedure {:inline 1} $LtBv128(src1: bv128, src2: bv128) returns (dst: bool)
{
    dst := $Lt'Bv128'(src1,src2);
}

procedure {:inline 1} $LeBv128(src1: bv128, src2: bv128) returns (dst: bool)
{
    dst := $Le'Bv128'(src1,src2);
}

procedure {:inline 1} $GtBv128(src1: bv128, src2: bv128) returns (dst: bool)
{
    dst := $Gt'Bv128'(src1,src2);
}

procedure {:inline 1} $GeBv128(src1: bv128, src2: bv128) returns (dst: bool)
{
    dst := $Ge'Bv128'(src1,src2);
}

function $IsValid'bv128'(v: bv128): bool {
  $Ge'Bv128'(v,0bv128) && $Le'Bv128'(v,340282366920938463463374607431768211455bv128)
}

function {:inline} $IsEqual'bv128'(x: bv128, y: bv128): bool {
    x == y
}

procedure {:inline 1} $int2bv128(src: int) returns (dst: bv128)
{
    if (src > 340282366920938463463374607431768211455) {
        call $ExecFailureAbort();
        return;
    }
    dst := $int2bv.128(src);
}

procedure {:inline 1} $bv2int128(src: bv128) returns (dst: int)
{
    dst := $bv2int.128(src);
}

function {:builtin "(_ int2bv 128)"} $int2bv.128(i: int) returns (bv128);
function {:builtin "bv2nat"} $bv2int.128(i: bv128) returns (int);

function {:bvbuiltin "bvand"} $And'Bv256'(bv256,bv256) returns(bv256);
function {:bvbuiltin "bvor"} $Or'Bv256'(bv256,bv256) returns(bv256);
function {:bvbuiltin "bvxor"} $Xor'Bv256'(bv256,bv256) returns(bv256);
function {:bvbuiltin "bvadd"} $Add'Bv256'(bv256,bv256) returns(bv256);
function {:bvbuiltin "bvsub"} $Sub'Bv256'(bv256,bv256) returns(bv256);
function {:bvbuiltin "bvmul"} $Mul'Bv256'(bv256,bv256) returns(bv256);
function {:bvbuiltin "bvudiv"} $Div'Bv256'(bv256,bv256) returns(bv256);
function {:bvbuiltin "bvurem"} $Mod'Bv256'(bv256,bv256) returns(bv256);
function {:bvbuiltin "bvshl"} $Shl'Bv256'(bv256,bv256) returns(bv256);
function {:bvbuiltin "bvlshr"} $Shr'Bv256'(bv256,bv256) returns(bv256);
function {:bvbuiltin "bvult"} $Lt'Bv256'(bv256,bv256) returns(bool);
function {:bvbuiltin "bvule"} $Le'Bv256'(bv256,bv256) returns(bool);
function {:bvbuiltin "bvugt"} $Gt'Bv256'(bv256,bv256) returns(bool);
function {:bvbuiltin "bvuge"} $Ge'Bv256'(bv256,bv256) returns(bool);

procedure {:inline 1} $AddBv256(src1: bv256, src2: bv256) returns (dst: bv256)
{
    if ($Lt'Bv256'($Add'Bv256'(src1, src2), src1)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Add'Bv256'(src1, src2);
}

procedure {:inline 1} $AddBv256_unchecked(src1: bv256, src2: bv256) returns (dst: bv256)
{
    dst := $Add'Bv256'(src1, src2);
}

procedure {:inline 1} $SubBv256(src1: bv256, src2: bv256) returns (dst: bv256)
{
    if ($Lt'Bv256'(src1, src2)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Sub'Bv256'(src1, src2);
}

procedure {:inline 1} $MulBv256(src1: bv256, src2: bv256) returns (dst: bv256)
{
    if ($Lt'Bv256'($Mul'Bv256'(src1, src2), src1)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Mul'Bv256'(src1, src2);
}

procedure {:inline 1} $DivBv256(src1: bv256, src2: bv256) returns (dst: bv256)
{
    if (src2 == 0bv256) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Div'Bv256'(src1, src2);
}

procedure {:inline 1} $ModBv256(src1: bv256, src2: bv256) returns (dst: bv256)
{
    if (src2 == 0bv256) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Mod'Bv256'(src1, src2);
}

procedure {:inline 1} $AndBv256(src1: bv256, src2: bv256) returns (dst: bv256)
{
    dst := $And'Bv256'(src1,src2);
}

procedure {:inline 1} $OrBv256(src1: bv256, src2: bv256) returns (dst: bv256)
{
    dst := $Or'Bv256'(src1,src2);
}

procedure {:inline 1} $XorBv256(src1: bv256, src2: bv256) returns (dst: bv256)
{
    dst := $Xor'Bv256'(src1,src2);
}

procedure {:inline 1} $LtBv256(src1: bv256, src2: bv256) returns (dst: bool)
{
    dst := $Lt'Bv256'(src1,src2);
}

procedure {:inline 1} $LeBv256(src1: bv256, src2: bv256) returns (dst: bool)
{
    dst := $Le'Bv256'(src1,src2);
}

procedure {:inline 1} $GtBv256(src1: bv256, src2: bv256) returns (dst: bool)
{
    dst := $Gt'Bv256'(src1,src2);
}

procedure {:inline 1} $GeBv256(src1: bv256, src2: bv256) returns (dst: bool)
{
    dst := $Ge'Bv256'(src1,src2);
}

function $IsValid'bv256'(v: bv256): bool {
  $Ge'Bv256'(v,0bv256) && $Le'Bv256'(v,115792089237316195423570985008687907853269984665640564039457584007913129639935bv256)
}

function {:inline} $IsEqual'bv256'(x: bv256, y: bv256): bool {
    x == y
}

procedure {:inline 1} $int2bv256(src: int) returns (dst: bv256)
{
    if (src > 115792089237316195423570985008687907853269984665640564039457584007913129639935) {
        call $ExecFailureAbort();
        return;
    }
    dst := $int2bv.256(src);
}

procedure {:inline 1} $bv2int256(src: bv256) returns (dst: int)
{
    dst := $bv2int.256(src);
}

function {:builtin "(_ int2bv 256)"} $int2bv.256(i: int) returns (bv256);
function {:builtin "bv2nat"} $bv2int.256(i: bv256) returns (int);

type {:datatype} $Range;
function {:constructor} $Range(lb: int, ub: int): $Range;

function {:inline} $IsValid'bool'(v: bool): bool {
  true
}

function $IsValid'u8'(v: int): bool {
  v >= 0 && v <= $MAX_U8
}

function $IsValid'u16'(v: int): bool {
  v >= 0 && v <= $MAX_U16
}

function $IsValid'u32'(v: int): bool {
  v >= 0 && v <= $MAX_U32
}

function $IsValid'u64'(v: int): bool {
  v >= 0 && v <= $MAX_U64
}

function $IsValid'u128'(v: int): bool {
  v >= 0 && v <= $MAX_U128
}

function $IsValid'u256'(v: int): bool {
  v >= 0 && v <= $MAX_U256
}

function $IsValid'num'(v: int): bool {
  true
}

function $IsValid'address'(v: int): bool {
  // TODO: restrict max to representable addresses?
  v >= 0
}

function {:inline} $IsValidRange(r: $Range): bool {
   $IsValid'u64'(lb#$Range(r)) &&  $IsValid'u64'(ub#$Range(r))
}

// Intentionally not inlined so it serves as a trigger in quantifiers.
function $InRange(r: $Range, i: int): bool {
   lb#$Range(r) <= i && i < ub#$Range(r)
}


function {:inline} $IsEqual'u8'(x: int, y: int): bool {
    x == y
}

function {:inline} $IsEqual'u16'(x: int, y: int): bool {
    x == y
}

function {:inline} $IsEqual'u32'(x: int, y: int): bool {
    x == y
}

function {:inline} $IsEqual'u64'(x: int, y: int): bool {
    x == y
}

function {:inline} $IsEqual'u128'(x: int, y: int): bool {
    x == y
}

function {:inline} $IsEqual'u256'(x: int, y: int): bool {
    x == y
}

function {:inline} $IsEqual'num'(x: int, y: int): bool {
    x == y
}

function {:inline} $IsEqual'address'(x: int, y: int): bool {
    x == y
}

function {:inline} $IsEqual'bool'(x: bool, y: bool): bool {
    x == y
}

// ============================================================================================
// Memory

type {:datatype} $Location;

// A global resource location within the statically known resource type's memory,
// where `a` is an address.
function {:constructor} $Global(a: int): $Location;

// A local location. `i` is the unique index of the local.
function {:constructor} $Local(i: int): $Location;

// The location of a reference outside of the verification scope, for example, a `&mut` parameter
// of the function being verified. References with these locations don't need to be written back
// when mutation ends.
function {:constructor} $Param(i: int): $Location;

// The location of an uninitialized mutation. Using this to make sure that the location
// will not be equal to any valid mutation locations, i.e., $Local, $Global, or $Param.
function {:constructor} $Uninitialized(): $Location;

// A mutable reference which also carries its current value. Since mutable references
// are single threaded in Move, we can keep them together and treat them as a value
// during mutation until the point they are stored back to their original location.
type {:datatype} $Mutation _;
function {:constructor} $Mutation<T>(l: $Location, p: Vec int, v: T): $Mutation T;

// Representation of memory for a given type.
type {:datatype} $Memory _;
function {:constructor} $Memory<T>(domain: [int]bool, contents: [int]T): $Memory T;

function {:builtin "MapConst"} $ConstMemoryDomain(v: bool): [int]bool;
function {:builtin "MapConst"} $ConstMemoryContent<T>(v: T): [int]T;
axiom $ConstMemoryDomain(false) == (lambda i: int :: false);
axiom $ConstMemoryDomain(true) == (lambda i: int :: true);


// Dereferences a mutation.
function {:inline} $Dereference<T>(ref: $Mutation T): T {
    v#$Mutation(ref)
}

// Update the value of a mutation.
function {:inline} $UpdateMutation<T>(m: $Mutation T, v: T): $Mutation T {
    $Mutation(l#$Mutation(m), p#$Mutation(m), v)
}

function {:inline} $ChildMutation<T1, T2>(m: $Mutation T1, offset: int, v: T2): $Mutation T2 {
    $Mutation(l#$Mutation(m), ExtendVec(p#$Mutation(m), offset), v)
}

// Return true if two mutations share the location and path
function {:inline} $IsSameMutation<T1, T2>(parent: $Mutation T1, child: $Mutation T2 ): bool {
    l#$Mutation(parent) == l#$Mutation(child) && p#$Mutation(parent) == p#$Mutation(child)
}

// Return true if the mutation is a parent of a child which was derived with the given edge offset. This
// is used to implement write-back choices.
function {:inline} $IsParentMutation<T1, T2>(parent: $Mutation T1, edge: int, child: $Mutation T2 ): bool {
    l#$Mutation(parent) == l#$Mutation(child) &&
    (var pp := p#$Mutation(parent);
    (var cp := p#$Mutation(child);
    (var pl := LenVec(pp);
    (var cl := LenVec(cp);
     cl == pl + 1 &&
     (forall i: int:: i >= 0 && i < pl ==> ReadVec(pp, i) ==  ReadVec(cp, i)) &&
     $EdgeMatches(ReadVec(cp, pl), edge)
    ))))
}

// Return true if the mutation is a parent of a child, for hyper edge.
function {:inline} $IsParentMutationHyper<T1, T2>(parent: $Mutation T1, hyper_edge: Vec int, child: $Mutation T2 ): bool {
    l#$Mutation(parent) == l#$Mutation(child) &&
    (var pp := p#$Mutation(parent);
    (var cp := p#$Mutation(child);
    (var pl := LenVec(pp);
    (var cl := LenVec(cp);
    (var el := LenVec(hyper_edge);
     cl == pl + el &&
     (forall i: int:: i >= 0 && i < pl ==> ReadVec(pp, i) == ReadVec(cp, i)) &&
     (forall i: int:: i >= 0 && i < el ==> $EdgeMatches(ReadVec(cp, pl + i), ReadVec(hyper_edge, i)))
    )))))
}

function {:inline} $EdgeMatches(edge: int, edge_pattern: int): bool {
    edge_pattern == -1 // wildcard
    || edge_pattern == edge
}



function {:inline} $SameLocation<T1, T2>(m1: $Mutation T1, m2: $Mutation T2): bool {
    l#$Mutation(m1) == l#$Mutation(m2)
}

function {:inline} $HasGlobalLocation<T>(m: $Mutation T): bool {
    is#$Global(l#$Mutation(m))
}

function {:inline} $HasLocalLocation<T>(m: $Mutation T, idx: int): bool {
    l#$Mutation(m) == $Local(idx)
}

function {:inline} $GlobalLocationAddress<T>(m: $Mutation T): int {
    a#$Global(l#$Mutation(m))
}



// Tests whether resource exists.
function {:inline} $ResourceExists<T>(m: $Memory T, addr: int): bool {
    domain#$Memory(m)[addr]
}

// Obtains Value of given resource.
function {:inline} $ResourceValue<T>(m: $Memory T, addr: int): T {
    contents#$Memory(m)[addr]
}

// Update resource.
function {:inline} $ResourceUpdate<T>(m: $Memory T, a: int, v: T): $Memory T {
    $Memory(domain#$Memory(m)[a := true], contents#$Memory(m)[a := v])
}

// Remove resource.
function {:inline} $ResourceRemove<T>(m: $Memory T, a: int): $Memory T {
    $Memory(domain#$Memory(m)[a := false], contents#$Memory(m))
}

// Copies resource from memory s to m.
function {:inline} $ResourceCopy<T>(m: $Memory T, s: $Memory T, a: int): $Memory T {
    $Memory(domain#$Memory(m)[a := domain#$Memory(s)[a]],
            contents#$Memory(m)[a := contents#$Memory(s)[a]])
}



// ============================================================================================
// Abort Handling

var $abort_flag: bool;
var $abort_code: int;

function {:inline} $process_abort_code(code: int): int {
    code
}

const $EXEC_FAILURE_CODE: int;
axiom $EXEC_FAILURE_CODE == -1;

// TODO(wrwg): currently we map aborts of native functions like those for vectors also to
//   execution failure. This may need to be aligned with what the runtime actually does.

procedure {:inline 1} $ExecFailureAbort() {
    $abort_flag := true;
    $abort_code := $EXEC_FAILURE_CODE;
}

procedure {:inline 1} $Abort(code: int) {
    $abort_flag := true;
    $abort_code := code;
}

function {:inline} $StdError(cat: int, reason: int): int {
    reason * 256 + cat
}

procedure {:inline 1} $InitVerification() {
    // Set abort_flag to false, and havoc abort_code
    $abort_flag := false;
    havoc $abort_code;
    // Initialize event store
    call $InitEventStore();
}

// ============================================================================================
// Instructions


procedure {:inline 1} $CastU8(src: int) returns (dst: int)
{
    if (src > $MAX_U8) {
        call $ExecFailureAbort();
        return;
    }
    dst := src;
}

procedure {:inline 1} $CastU16(src: int) returns (dst: int)
{
    if (src > $MAX_U16) {
        call $ExecFailureAbort();
        return;
    }
    dst := src;
}

procedure {:inline 1} $CastU32(src: int) returns (dst: int)
{
    if (src > $MAX_U32) {
        call $ExecFailureAbort();
        return;
    }
    dst := src;
}

procedure {:inline 1} $CastU64(src: int) returns (dst: int)
{
    if (src > $MAX_U64) {
        call $ExecFailureAbort();
        return;
    }
    dst := src;
}

procedure {:inline 1} $CastU128(src: int) returns (dst: int)
{
    if (src > $MAX_U128) {
        call $ExecFailureAbort();
        return;
    }
    dst := src;
}

procedure {:inline 1} $CastU256(src: int) returns (dst: int)
{
    if (src > $MAX_U256) {
        call $ExecFailureAbort();
        return;
    }
    dst := src;
}

procedure {:inline 1} $AddU8(src1: int, src2: int) returns (dst: int)
{
    if (src1 + src2 > $MAX_U8) {
        call $ExecFailureAbort();
        return;
    }
    dst := src1 + src2;
}

procedure {:inline 1} $AddU16(src1: int, src2: int) returns (dst: int)
{
    if (src1 + src2 > $MAX_U16) {
        call $ExecFailureAbort();
        return;
    }
    dst := src1 + src2;
}

procedure {:inline 1} $AddU16_unchecked(src1: int, src2: int) returns (dst: int)
{
    dst := src1 + src2;
}

procedure {:inline 1} $AddU32(src1: int, src2: int) returns (dst: int)
{
    if (src1 + src2 > $MAX_U32) {
        call $ExecFailureAbort();
        return;
    }
    dst := src1 + src2;
}

procedure {:inline 1} $AddU32_unchecked(src1: int, src2: int) returns (dst: int)
{
    dst := src1 + src2;
}

procedure {:inline 1} $AddU64(src1: int, src2: int) returns (dst: int)
{
    if (src1 + src2 > $MAX_U64) {
        call $ExecFailureAbort();
        return;
    }
    dst := src1 + src2;
}

procedure {:inline 1} $AddU64_unchecked(src1: int, src2: int) returns (dst: int)
{
    dst := src1 + src2;
}

procedure {:inline 1} $AddU128(src1: int, src2: int) returns (dst: int)
{
    if (src1 + src2 > $MAX_U128) {
        call $ExecFailureAbort();
        return;
    }
    dst := src1 + src2;
}

procedure {:inline 1} $AddU128_unchecked(src1: int, src2: int) returns (dst: int)
{
    dst := src1 + src2;
}

procedure {:inline 1} $AddU256(src1: int, src2: int) returns (dst: int)
{
    if (src1 + src2 > $MAX_U256) {
        call $ExecFailureAbort();
        return;
    }
    dst := src1 + src2;
}

procedure {:inline 1} $AddU256_unchecked(src1: int, src2: int) returns (dst: int)
{
    dst := src1 + src2;
}

procedure {:inline 1} $Sub(src1: int, src2: int) returns (dst: int)
{
    if (src1 < src2) {
        call $ExecFailureAbort();
        return;
    }
    dst := src1 - src2;
}

// uninterpreted function to return an undefined value.
function $undefined_int(): int;

// Recursive exponentiation function
// Undefined unless e >=0.  $pow(0,0) is also undefined.
function $pow(n: int, e: int): int {
    if n != 0 && e == 0 then 1
    else if e > 0 then n * $pow(n, e - 1)
    else $undefined_int()
}

function $shl(src1: int, p: int): int {
    src1 * $pow(2, p)
}

function $shlU8(src1: int, p: int): int {
    (src1 * $pow(2, p)) mod 256
}

function $shlU16(src1: int, p: int): int {
    (src1 * $pow(2, p)) mod 65536
}

function $shlU32(src1: int, p: int): int {
    (src1 * $pow(2, p)) mod 4294967296
}

function $shlU64(src1: int, p: int): int {
    (src1 * $pow(2, p)) mod 18446744073709551616
}

function $shlU128(src1: int, p: int): int {
    (src1 * $pow(2, p)) mod 340282366920938463463374607431768211456
}

function $shlU256(src1: int, p: int): int {
    (src1 * $pow(2, p)) mod 115792089237316195423570985008687907853269984665640564039457584007913129639936
}

function $shr(src1: int, p: int): int {
    src1 div $pow(2, p)
}

// We need to know the size of the destination in order to drop bits
// that have been shifted left more than that, so we have $ShlU8/16/32/64/128/256
procedure {:inline 1} $ShlU8(src1: int, src2: int) returns (dst: int)
{
    var res: int;
    // src2 is a u8
    assume src2 >= 0 && src2 < 256;
    if (src2 >= 8) {
        call $ExecFailureAbort();
        return;
    }
    dst := $shlU8(src1, src2);
}

// Template for cast and shift operations of bitvector types

procedure {:inline 1} $CastBv8to8(src: bv8) returns (dst: bv8)
{
    dst := src;
}


function $shlBv8From8(src1: bv8, src2: bv8) returns (bv8)
{
    $Shl'Bv8'(src1, src2)
}

procedure {:inline 1} $ShlBv8From8(src1: bv8, src2: bv8) returns (dst: bv8)
{
    if ($Ge'Bv8'(src2, 8bv8)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shl'Bv8'(src1, src2);
}

function $shrBv8From8(src1: bv8, src2: bv8) returns (bv8)
{
    $Shr'Bv8'(src1, src2)
}

procedure {:inline 1} $ShrBv8From8(src1: bv8, src2: bv8) returns (dst: bv8)
{
    if ($Ge'Bv8'(src2, 8bv8)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shr'Bv8'(src1, src2);
}

procedure {:inline 1} $CastBv16to8(src: bv16) returns (dst: bv8)
{
    if ($Gt'Bv16'(src, 255bv16)) {
            call $ExecFailureAbort();
            return;
    }
    dst := src[8:0];
}


function $shlBv8From16(src1: bv8, src2: bv16) returns (bv8)
{
    $Shl'Bv8'(src1, src2[8:0])
}

procedure {:inline 1} $ShlBv8From16(src1: bv8, src2: bv16) returns (dst: bv8)
{
    if ($Ge'Bv16'(src2, 8bv16)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shl'Bv8'(src1, src2[8:0]);
}

function $shrBv8From16(src1: bv8, src2: bv16) returns (bv8)
{
    $Shr'Bv8'(src1, src2[8:0])
}

procedure {:inline 1} $ShrBv8From16(src1: bv8, src2: bv16) returns (dst: bv8)
{
    if ($Ge'Bv16'(src2, 8bv16)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shr'Bv8'(src1, src2[8:0]);
}

procedure {:inline 1} $CastBv32to8(src: bv32) returns (dst: bv8)
{
    if ($Gt'Bv32'(src, 255bv32)) {
            call $ExecFailureAbort();
            return;
    }
    dst := src[8:0];
}


function $shlBv8From32(src1: bv8, src2: bv32) returns (bv8)
{
    $Shl'Bv8'(src1, src2[8:0])
}

procedure {:inline 1} $ShlBv8From32(src1: bv8, src2: bv32) returns (dst: bv8)
{
    if ($Ge'Bv32'(src2, 8bv32)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shl'Bv8'(src1, src2[8:0]);
}

function $shrBv8From32(src1: bv8, src2: bv32) returns (bv8)
{
    $Shr'Bv8'(src1, src2[8:0])
}

procedure {:inline 1} $ShrBv8From32(src1: bv8, src2: bv32) returns (dst: bv8)
{
    if ($Ge'Bv32'(src2, 8bv32)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shr'Bv8'(src1, src2[8:0]);
}

procedure {:inline 1} $CastBv64to8(src: bv64) returns (dst: bv8)
{
    if ($Gt'Bv64'(src, 255bv64)) {
            call $ExecFailureAbort();
            return;
    }
    dst := src[8:0];
}


function $shlBv8From64(src1: bv8, src2: bv64) returns (bv8)
{
    $Shl'Bv8'(src1, src2[8:0])
}

procedure {:inline 1} $ShlBv8From64(src1: bv8, src2: bv64) returns (dst: bv8)
{
    if ($Ge'Bv64'(src2, 8bv64)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shl'Bv8'(src1, src2[8:0]);
}

function $shrBv8From64(src1: bv8, src2: bv64) returns (bv8)
{
    $Shr'Bv8'(src1, src2[8:0])
}

procedure {:inline 1} $ShrBv8From64(src1: bv8, src2: bv64) returns (dst: bv8)
{
    if ($Ge'Bv64'(src2, 8bv64)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shr'Bv8'(src1, src2[8:0]);
}

procedure {:inline 1} $CastBv128to8(src: bv128) returns (dst: bv8)
{
    if ($Gt'Bv128'(src, 255bv128)) {
            call $ExecFailureAbort();
            return;
    }
    dst := src[8:0];
}


function $shlBv8From128(src1: bv8, src2: bv128) returns (bv8)
{
    $Shl'Bv8'(src1, src2[8:0])
}

procedure {:inline 1} $ShlBv8From128(src1: bv8, src2: bv128) returns (dst: bv8)
{
    if ($Ge'Bv128'(src2, 8bv128)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shl'Bv8'(src1, src2[8:0]);
}

function $shrBv8From128(src1: bv8, src2: bv128) returns (bv8)
{
    $Shr'Bv8'(src1, src2[8:0])
}

procedure {:inline 1} $ShrBv8From128(src1: bv8, src2: bv128) returns (dst: bv8)
{
    if ($Ge'Bv128'(src2, 8bv128)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shr'Bv8'(src1, src2[8:0]);
}

procedure {:inline 1} $CastBv256to8(src: bv256) returns (dst: bv8)
{
    if ($Gt'Bv256'(src, 255bv256)) {
            call $ExecFailureAbort();
            return;
    }
    dst := src[8:0];
}


function $shlBv8From256(src1: bv8, src2: bv256) returns (bv8)
{
    $Shl'Bv8'(src1, src2[8:0])
}

procedure {:inline 1} $ShlBv8From256(src1: bv8, src2: bv256) returns (dst: bv8)
{
    if ($Ge'Bv256'(src2, 8bv256)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shl'Bv8'(src1, src2[8:0]);
}

function $shrBv8From256(src1: bv8, src2: bv256) returns (bv8)
{
    $Shr'Bv8'(src1, src2[8:0])
}

procedure {:inline 1} $ShrBv8From256(src1: bv8, src2: bv256) returns (dst: bv8)
{
    if ($Ge'Bv256'(src2, 8bv256)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shr'Bv8'(src1, src2[8:0]);
}

procedure {:inline 1} $CastBv8to16(src: bv8) returns (dst: bv16)
{
    dst := 0bv8 ++ src;
}


function $shlBv16From8(src1: bv16, src2: bv8) returns (bv16)
{
    $Shl'Bv16'(src1, 0bv8 ++ src2)
}

procedure {:inline 1} $ShlBv16From8(src1: bv16, src2: bv8) returns (dst: bv16)
{
    if ($Ge'Bv8'(src2, 16bv8)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shl'Bv16'(src1, 0bv8 ++ src2);
}

function $shrBv16From8(src1: bv16, src2: bv8) returns (bv16)
{
    $Shr'Bv16'(src1, 0bv8 ++ src2)
}

procedure {:inline 1} $ShrBv16From8(src1: bv16, src2: bv8) returns (dst: bv16)
{
    if ($Ge'Bv8'(src2, 16bv8)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shr'Bv16'(src1, 0bv8 ++ src2);
}

procedure {:inline 1} $CastBv16to16(src: bv16) returns (dst: bv16)
{
    dst := src;
}


function $shlBv16From16(src1: bv16, src2: bv16) returns (bv16)
{
    $Shl'Bv16'(src1, src2)
}

procedure {:inline 1} $ShlBv16From16(src1: bv16, src2: bv16) returns (dst: bv16)
{
    if ($Ge'Bv16'(src2, 16bv16)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shl'Bv16'(src1, src2);
}

function $shrBv16From16(src1: bv16, src2: bv16) returns (bv16)
{
    $Shr'Bv16'(src1, src2)
}

procedure {:inline 1} $ShrBv16From16(src1: bv16, src2: bv16) returns (dst: bv16)
{
    if ($Ge'Bv16'(src2, 16bv16)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shr'Bv16'(src1, src2);
}

procedure {:inline 1} $CastBv32to16(src: bv32) returns (dst: bv16)
{
    if ($Gt'Bv32'(src, 65535bv32)) {
            call $ExecFailureAbort();
            return;
    }
    dst := src[16:0];
}


function $shlBv16From32(src1: bv16, src2: bv32) returns (bv16)
{
    $Shl'Bv16'(src1, src2[16:0])
}

procedure {:inline 1} $ShlBv16From32(src1: bv16, src2: bv32) returns (dst: bv16)
{
    if ($Ge'Bv32'(src2, 16bv32)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shl'Bv16'(src1, src2[16:0]);
}

function $shrBv16From32(src1: bv16, src2: bv32) returns (bv16)
{
    $Shr'Bv16'(src1, src2[16:0])
}

procedure {:inline 1} $ShrBv16From32(src1: bv16, src2: bv32) returns (dst: bv16)
{
    if ($Ge'Bv32'(src2, 16bv32)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shr'Bv16'(src1, src2[16:0]);
}

procedure {:inline 1} $CastBv64to16(src: bv64) returns (dst: bv16)
{
    if ($Gt'Bv64'(src, 65535bv64)) {
            call $ExecFailureAbort();
            return;
    }
    dst := src[16:0];
}


function $shlBv16From64(src1: bv16, src2: bv64) returns (bv16)
{
    $Shl'Bv16'(src1, src2[16:0])
}

procedure {:inline 1} $ShlBv16From64(src1: bv16, src2: bv64) returns (dst: bv16)
{
    if ($Ge'Bv64'(src2, 16bv64)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shl'Bv16'(src1, src2[16:0]);
}

function $shrBv16From64(src1: bv16, src2: bv64) returns (bv16)
{
    $Shr'Bv16'(src1, src2[16:0])
}

procedure {:inline 1} $ShrBv16From64(src1: bv16, src2: bv64) returns (dst: bv16)
{
    if ($Ge'Bv64'(src2, 16bv64)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shr'Bv16'(src1, src2[16:0]);
}

procedure {:inline 1} $CastBv128to16(src: bv128) returns (dst: bv16)
{
    if ($Gt'Bv128'(src, 65535bv128)) {
            call $ExecFailureAbort();
            return;
    }
    dst := src[16:0];
}


function $shlBv16From128(src1: bv16, src2: bv128) returns (bv16)
{
    $Shl'Bv16'(src1, src2[16:0])
}

procedure {:inline 1} $ShlBv16From128(src1: bv16, src2: bv128) returns (dst: bv16)
{
    if ($Ge'Bv128'(src2, 16bv128)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shl'Bv16'(src1, src2[16:0]);
}

function $shrBv16From128(src1: bv16, src2: bv128) returns (bv16)
{
    $Shr'Bv16'(src1, src2[16:0])
}

procedure {:inline 1} $ShrBv16From128(src1: bv16, src2: bv128) returns (dst: bv16)
{
    if ($Ge'Bv128'(src2, 16bv128)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shr'Bv16'(src1, src2[16:0]);
}

procedure {:inline 1} $CastBv256to16(src: bv256) returns (dst: bv16)
{
    if ($Gt'Bv256'(src, 65535bv256)) {
            call $ExecFailureAbort();
            return;
    }
    dst := src[16:0];
}


function $shlBv16From256(src1: bv16, src2: bv256) returns (bv16)
{
    $Shl'Bv16'(src1, src2[16:0])
}

procedure {:inline 1} $ShlBv16From256(src1: bv16, src2: bv256) returns (dst: bv16)
{
    if ($Ge'Bv256'(src2, 16bv256)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shl'Bv16'(src1, src2[16:0]);
}

function $shrBv16From256(src1: bv16, src2: bv256) returns (bv16)
{
    $Shr'Bv16'(src1, src2[16:0])
}

procedure {:inline 1} $ShrBv16From256(src1: bv16, src2: bv256) returns (dst: bv16)
{
    if ($Ge'Bv256'(src2, 16bv256)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shr'Bv16'(src1, src2[16:0]);
}

procedure {:inline 1} $CastBv8to32(src: bv8) returns (dst: bv32)
{
    dst := 0bv24 ++ src;
}


function $shlBv32From8(src1: bv32, src2: bv8) returns (bv32)
{
    $Shl'Bv32'(src1, 0bv24 ++ src2)
}

procedure {:inline 1} $ShlBv32From8(src1: bv32, src2: bv8) returns (dst: bv32)
{
    if ($Ge'Bv8'(src2, 32bv8)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shl'Bv32'(src1, 0bv24 ++ src2);
}

function $shrBv32From8(src1: bv32, src2: bv8) returns (bv32)
{
    $Shr'Bv32'(src1, 0bv24 ++ src2)
}

procedure {:inline 1} $ShrBv32From8(src1: bv32, src2: bv8) returns (dst: bv32)
{
    if ($Ge'Bv8'(src2, 32bv8)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shr'Bv32'(src1, 0bv24 ++ src2);
}

procedure {:inline 1} $CastBv16to32(src: bv16) returns (dst: bv32)
{
    dst := 0bv16 ++ src;
}


function $shlBv32From16(src1: bv32, src2: bv16) returns (bv32)
{
    $Shl'Bv32'(src1, 0bv16 ++ src2)
}

procedure {:inline 1} $ShlBv32From16(src1: bv32, src2: bv16) returns (dst: bv32)
{
    if ($Ge'Bv16'(src2, 32bv16)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shl'Bv32'(src1, 0bv16 ++ src2);
}

function $shrBv32From16(src1: bv32, src2: bv16) returns (bv32)
{
    $Shr'Bv32'(src1, 0bv16 ++ src2)
}

procedure {:inline 1} $ShrBv32From16(src1: bv32, src2: bv16) returns (dst: bv32)
{
    if ($Ge'Bv16'(src2, 32bv16)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shr'Bv32'(src1, 0bv16 ++ src2);
}

procedure {:inline 1} $CastBv32to32(src: bv32) returns (dst: bv32)
{
    dst := src;
}


function $shlBv32From32(src1: bv32, src2: bv32) returns (bv32)
{
    $Shl'Bv32'(src1, src2)
}

procedure {:inline 1} $ShlBv32From32(src1: bv32, src2: bv32) returns (dst: bv32)
{
    if ($Ge'Bv32'(src2, 32bv32)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shl'Bv32'(src1, src2);
}

function $shrBv32From32(src1: bv32, src2: bv32) returns (bv32)
{
    $Shr'Bv32'(src1, src2)
}

procedure {:inline 1} $ShrBv32From32(src1: bv32, src2: bv32) returns (dst: bv32)
{
    if ($Ge'Bv32'(src2, 32bv32)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shr'Bv32'(src1, src2);
}

procedure {:inline 1} $CastBv64to32(src: bv64) returns (dst: bv32)
{
    if ($Gt'Bv64'(src, 2147483647bv64)) {
            call $ExecFailureAbort();
            return;
    }
    dst := src[32:0];
}


function $shlBv32From64(src1: bv32, src2: bv64) returns (bv32)
{
    $Shl'Bv32'(src1, src2[32:0])
}

procedure {:inline 1} $ShlBv32From64(src1: bv32, src2: bv64) returns (dst: bv32)
{
    if ($Ge'Bv64'(src2, 32bv64)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shl'Bv32'(src1, src2[32:0]);
}

function $shrBv32From64(src1: bv32, src2: bv64) returns (bv32)
{
    $Shr'Bv32'(src1, src2[32:0])
}

procedure {:inline 1} $ShrBv32From64(src1: bv32, src2: bv64) returns (dst: bv32)
{
    if ($Ge'Bv64'(src2, 32bv64)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shr'Bv32'(src1, src2[32:0]);
}

procedure {:inline 1} $CastBv128to32(src: bv128) returns (dst: bv32)
{
    if ($Gt'Bv128'(src, 2147483647bv128)) {
            call $ExecFailureAbort();
            return;
    }
    dst := src[32:0];
}


function $shlBv32From128(src1: bv32, src2: bv128) returns (bv32)
{
    $Shl'Bv32'(src1, src2[32:0])
}

procedure {:inline 1} $ShlBv32From128(src1: bv32, src2: bv128) returns (dst: bv32)
{
    if ($Ge'Bv128'(src2, 32bv128)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shl'Bv32'(src1, src2[32:0]);
}

function $shrBv32From128(src1: bv32, src2: bv128) returns (bv32)
{
    $Shr'Bv32'(src1, src2[32:0])
}

procedure {:inline 1} $ShrBv32From128(src1: bv32, src2: bv128) returns (dst: bv32)
{
    if ($Ge'Bv128'(src2, 32bv128)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shr'Bv32'(src1, src2[32:0]);
}

procedure {:inline 1} $CastBv256to32(src: bv256) returns (dst: bv32)
{
    if ($Gt'Bv256'(src, 2147483647bv256)) {
            call $ExecFailureAbort();
            return;
    }
    dst := src[32:0];
}


function $shlBv32From256(src1: bv32, src2: bv256) returns (bv32)
{
    $Shl'Bv32'(src1, src2[32:0])
}

procedure {:inline 1} $ShlBv32From256(src1: bv32, src2: bv256) returns (dst: bv32)
{
    if ($Ge'Bv256'(src2, 32bv256)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shl'Bv32'(src1, src2[32:0]);
}

function $shrBv32From256(src1: bv32, src2: bv256) returns (bv32)
{
    $Shr'Bv32'(src1, src2[32:0])
}

procedure {:inline 1} $ShrBv32From256(src1: bv32, src2: bv256) returns (dst: bv32)
{
    if ($Ge'Bv256'(src2, 32bv256)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shr'Bv32'(src1, src2[32:0]);
}

procedure {:inline 1} $CastBv8to64(src: bv8) returns (dst: bv64)
{
    dst := 0bv56 ++ src;
}


function $shlBv64From8(src1: bv64, src2: bv8) returns (bv64)
{
    $Shl'Bv64'(src1, 0bv56 ++ src2)
}

procedure {:inline 1} $ShlBv64From8(src1: bv64, src2: bv8) returns (dst: bv64)
{
    if ($Ge'Bv8'(src2, 64bv8)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shl'Bv64'(src1, 0bv56 ++ src2);
}

function $shrBv64From8(src1: bv64, src2: bv8) returns (bv64)
{
    $Shr'Bv64'(src1, 0bv56 ++ src2)
}

procedure {:inline 1} $ShrBv64From8(src1: bv64, src2: bv8) returns (dst: bv64)
{
    if ($Ge'Bv8'(src2, 64bv8)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shr'Bv64'(src1, 0bv56 ++ src2);
}

procedure {:inline 1} $CastBv16to64(src: bv16) returns (dst: bv64)
{
    dst := 0bv48 ++ src;
}


function $shlBv64From16(src1: bv64, src2: bv16) returns (bv64)
{
    $Shl'Bv64'(src1, 0bv48 ++ src2)
}

procedure {:inline 1} $ShlBv64From16(src1: bv64, src2: bv16) returns (dst: bv64)
{
    if ($Ge'Bv16'(src2, 64bv16)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shl'Bv64'(src1, 0bv48 ++ src2);
}

function $shrBv64From16(src1: bv64, src2: bv16) returns (bv64)
{
    $Shr'Bv64'(src1, 0bv48 ++ src2)
}

procedure {:inline 1} $ShrBv64From16(src1: bv64, src2: bv16) returns (dst: bv64)
{
    if ($Ge'Bv16'(src2, 64bv16)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shr'Bv64'(src1, 0bv48 ++ src2);
}

procedure {:inline 1} $CastBv32to64(src: bv32) returns (dst: bv64)
{
    dst := 0bv32 ++ src;
}


function $shlBv64From32(src1: bv64, src2: bv32) returns (bv64)
{
    $Shl'Bv64'(src1, 0bv32 ++ src2)
}

procedure {:inline 1} $ShlBv64From32(src1: bv64, src2: bv32) returns (dst: bv64)
{
    if ($Ge'Bv32'(src2, 64bv32)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shl'Bv64'(src1, 0bv32 ++ src2);
}

function $shrBv64From32(src1: bv64, src2: bv32) returns (bv64)
{
    $Shr'Bv64'(src1, 0bv32 ++ src2)
}

procedure {:inline 1} $ShrBv64From32(src1: bv64, src2: bv32) returns (dst: bv64)
{
    if ($Ge'Bv32'(src2, 64bv32)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shr'Bv64'(src1, 0bv32 ++ src2);
}

procedure {:inline 1} $CastBv64to64(src: bv64) returns (dst: bv64)
{
    dst := src;
}


function $shlBv64From64(src1: bv64, src2: bv64) returns (bv64)
{
    $Shl'Bv64'(src1, src2)
}

procedure {:inline 1} $ShlBv64From64(src1: bv64, src2: bv64) returns (dst: bv64)
{
    if ($Ge'Bv64'(src2, 64bv64)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shl'Bv64'(src1, src2);
}

function $shrBv64From64(src1: bv64, src2: bv64) returns (bv64)
{
    $Shr'Bv64'(src1, src2)
}

procedure {:inline 1} $ShrBv64From64(src1: bv64, src2: bv64) returns (dst: bv64)
{
    if ($Ge'Bv64'(src2, 64bv64)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shr'Bv64'(src1, src2);
}

procedure {:inline 1} $CastBv128to64(src: bv128) returns (dst: bv64)
{
    if ($Gt'Bv128'(src, 18446744073709551615bv128)) {
            call $ExecFailureAbort();
            return;
    }
    dst := src[64:0];
}


function $shlBv64From128(src1: bv64, src2: bv128) returns (bv64)
{
    $Shl'Bv64'(src1, src2[64:0])
}

procedure {:inline 1} $ShlBv64From128(src1: bv64, src2: bv128) returns (dst: bv64)
{
    if ($Ge'Bv128'(src2, 64bv128)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shl'Bv64'(src1, src2[64:0]);
}

function $shrBv64From128(src1: bv64, src2: bv128) returns (bv64)
{
    $Shr'Bv64'(src1, src2[64:0])
}

procedure {:inline 1} $ShrBv64From128(src1: bv64, src2: bv128) returns (dst: bv64)
{
    if ($Ge'Bv128'(src2, 64bv128)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shr'Bv64'(src1, src2[64:0]);
}

procedure {:inline 1} $CastBv256to64(src: bv256) returns (dst: bv64)
{
    if ($Gt'Bv256'(src, 18446744073709551615bv256)) {
            call $ExecFailureAbort();
            return;
    }
    dst := src[64:0];
}


function $shlBv64From256(src1: bv64, src2: bv256) returns (bv64)
{
    $Shl'Bv64'(src1, src2[64:0])
}

procedure {:inline 1} $ShlBv64From256(src1: bv64, src2: bv256) returns (dst: bv64)
{
    if ($Ge'Bv256'(src2, 64bv256)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shl'Bv64'(src1, src2[64:0]);
}

function $shrBv64From256(src1: bv64, src2: bv256) returns (bv64)
{
    $Shr'Bv64'(src1, src2[64:0])
}

procedure {:inline 1} $ShrBv64From256(src1: bv64, src2: bv256) returns (dst: bv64)
{
    if ($Ge'Bv256'(src2, 64bv256)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shr'Bv64'(src1, src2[64:0]);
}

procedure {:inline 1} $CastBv8to128(src: bv8) returns (dst: bv128)
{
    dst := 0bv120 ++ src;
}


function $shlBv128From8(src1: bv128, src2: bv8) returns (bv128)
{
    $Shl'Bv128'(src1, 0bv120 ++ src2)
}

procedure {:inline 1} $ShlBv128From8(src1: bv128, src2: bv8) returns (dst: bv128)
{
    if ($Ge'Bv8'(src2, 128bv8)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shl'Bv128'(src1, 0bv120 ++ src2);
}

function $shrBv128From8(src1: bv128, src2: bv8) returns (bv128)
{
    $Shr'Bv128'(src1, 0bv120 ++ src2)
}

procedure {:inline 1} $ShrBv128From8(src1: bv128, src2: bv8) returns (dst: bv128)
{
    if ($Ge'Bv8'(src2, 128bv8)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shr'Bv128'(src1, 0bv120 ++ src2);
}

procedure {:inline 1} $CastBv16to128(src: bv16) returns (dst: bv128)
{
    dst := 0bv112 ++ src;
}


function $shlBv128From16(src1: bv128, src2: bv16) returns (bv128)
{
    $Shl'Bv128'(src1, 0bv112 ++ src2)
}

procedure {:inline 1} $ShlBv128From16(src1: bv128, src2: bv16) returns (dst: bv128)
{
    if ($Ge'Bv16'(src2, 128bv16)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shl'Bv128'(src1, 0bv112 ++ src2);
}

function $shrBv128From16(src1: bv128, src2: bv16) returns (bv128)
{
    $Shr'Bv128'(src1, 0bv112 ++ src2)
}

procedure {:inline 1} $ShrBv128From16(src1: bv128, src2: bv16) returns (dst: bv128)
{
    if ($Ge'Bv16'(src2, 128bv16)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shr'Bv128'(src1, 0bv112 ++ src2);
}

procedure {:inline 1} $CastBv32to128(src: bv32) returns (dst: bv128)
{
    dst := 0bv96 ++ src;
}


function $shlBv128From32(src1: bv128, src2: bv32) returns (bv128)
{
    $Shl'Bv128'(src1, 0bv96 ++ src2)
}

procedure {:inline 1} $ShlBv128From32(src1: bv128, src2: bv32) returns (dst: bv128)
{
    if ($Ge'Bv32'(src2, 128bv32)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shl'Bv128'(src1, 0bv96 ++ src2);
}

function $shrBv128From32(src1: bv128, src2: bv32) returns (bv128)
{
    $Shr'Bv128'(src1, 0bv96 ++ src2)
}

procedure {:inline 1} $ShrBv128From32(src1: bv128, src2: bv32) returns (dst: bv128)
{
    if ($Ge'Bv32'(src2, 128bv32)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shr'Bv128'(src1, 0bv96 ++ src2);
}

procedure {:inline 1} $CastBv64to128(src: bv64) returns (dst: bv128)
{
    dst := 0bv64 ++ src;
}


function $shlBv128From64(src1: bv128, src2: bv64) returns (bv128)
{
    $Shl'Bv128'(src1, 0bv64 ++ src2)
}

procedure {:inline 1} $ShlBv128From64(src1: bv128, src2: bv64) returns (dst: bv128)
{
    if ($Ge'Bv64'(src2, 128bv64)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shl'Bv128'(src1, 0bv64 ++ src2);
}

function $shrBv128From64(src1: bv128, src2: bv64) returns (bv128)
{
    $Shr'Bv128'(src1, 0bv64 ++ src2)
}

procedure {:inline 1} $ShrBv128From64(src1: bv128, src2: bv64) returns (dst: bv128)
{
    if ($Ge'Bv64'(src2, 128bv64)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shr'Bv128'(src1, 0bv64 ++ src2);
}

procedure {:inline 1} $CastBv128to128(src: bv128) returns (dst: bv128)
{
    dst := src;
}


function $shlBv128From128(src1: bv128, src2: bv128) returns (bv128)
{
    $Shl'Bv128'(src1, src2)
}

procedure {:inline 1} $ShlBv128From128(src1: bv128, src2: bv128) returns (dst: bv128)
{
    if ($Ge'Bv128'(src2, 128bv128)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shl'Bv128'(src1, src2);
}

function $shrBv128From128(src1: bv128, src2: bv128) returns (bv128)
{
    $Shr'Bv128'(src1, src2)
}

procedure {:inline 1} $ShrBv128From128(src1: bv128, src2: bv128) returns (dst: bv128)
{
    if ($Ge'Bv128'(src2, 128bv128)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shr'Bv128'(src1, src2);
}

procedure {:inline 1} $CastBv256to128(src: bv256) returns (dst: bv128)
{
    if ($Gt'Bv256'(src, 340282366920938463463374607431768211455bv256)) {
            call $ExecFailureAbort();
            return;
    }
    dst := src[128:0];
}


function $shlBv128From256(src1: bv128, src2: bv256) returns (bv128)
{
    $Shl'Bv128'(src1, src2[128:0])
}

procedure {:inline 1} $ShlBv128From256(src1: bv128, src2: bv256) returns (dst: bv128)
{
    if ($Ge'Bv256'(src2, 128bv256)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shl'Bv128'(src1, src2[128:0]);
}

function $shrBv128From256(src1: bv128, src2: bv256) returns (bv128)
{
    $Shr'Bv128'(src1, src2[128:0])
}

procedure {:inline 1} $ShrBv128From256(src1: bv128, src2: bv256) returns (dst: bv128)
{
    if ($Ge'Bv256'(src2, 128bv256)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shr'Bv128'(src1, src2[128:0]);
}

procedure {:inline 1} $CastBv8to256(src: bv8) returns (dst: bv256)
{
    dst := 0bv248 ++ src;
}


function $shlBv256From8(src1: bv256, src2: bv8) returns (bv256)
{
    $Shl'Bv256'(src1, 0bv248 ++ src2)
}

procedure {:inline 1} $ShlBv256From8(src1: bv256, src2: bv8) returns (dst: bv256)
{
    if ($Ge'Bv8'(src2, 256bv8)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shl'Bv256'(src1, 0bv248 ++ src2);
}

function $shrBv256From8(src1: bv256, src2: bv8) returns (bv256)
{
    $Shr'Bv256'(src1, 0bv248 ++ src2)
}

procedure {:inline 1} $ShrBv256From8(src1: bv256, src2: bv8) returns (dst: bv256)
{
    if ($Ge'Bv8'(src2, 256bv8)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shr'Bv256'(src1, 0bv248 ++ src2);
}

procedure {:inline 1} $CastBv16to256(src: bv16) returns (dst: bv256)
{
    dst := 0bv240 ++ src;
}


function $shlBv256From16(src1: bv256, src2: bv16) returns (bv256)
{
    $Shl'Bv256'(src1, 0bv240 ++ src2)
}

procedure {:inline 1} $ShlBv256From16(src1: bv256, src2: bv16) returns (dst: bv256)
{
    if ($Ge'Bv16'(src2, 256bv16)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shl'Bv256'(src1, 0bv240 ++ src2);
}

function $shrBv256From16(src1: bv256, src2: bv16) returns (bv256)
{
    $Shr'Bv256'(src1, 0bv240 ++ src2)
}

procedure {:inline 1} $ShrBv256From16(src1: bv256, src2: bv16) returns (dst: bv256)
{
    if ($Ge'Bv16'(src2, 256bv16)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shr'Bv256'(src1, 0bv240 ++ src2);
}

procedure {:inline 1} $CastBv32to256(src: bv32) returns (dst: bv256)
{
    dst := 0bv224 ++ src;
}


function $shlBv256From32(src1: bv256, src2: bv32) returns (bv256)
{
    $Shl'Bv256'(src1, 0bv224 ++ src2)
}

procedure {:inline 1} $ShlBv256From32(src1: bv256, src2: bv32) returns (dst: bv256)
{
    if ($Ge'Bv32'(src2, 256bv32)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shl'Bv256'(src1, 0bv224 ++ src2);
}

function $shrBv256From32(src1: bv256, src2: bv32) returns (bv256)
{
    $Shr'Bv256'(src1, 0bv224 ++ src2)
}

procedure {:inline 1} $ShrBv256From32(src1: bv256, src2: bv32) returns (dst: bv256)
{
    if ($Ge'Bv32'(src2, 256bv32)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shr'Bv256'(src1, 0bv224 ++ src2);
}

procedure {:inline 1} $CastBv64to256(src: bv64) returns (dst: bv256)
{
    dst := 0bv192 ++ src;
}


function $shlBv256From64(src1: bv256, src2: bv64) returns (bv256)
{
    $Shl'Bv256'(src1, 0bv192 ++ src2)
}

procedure {:inline 1} $ShlBv256From64(src1: bv256, src2: bv64) returns (dst: bv256)
{
    if ($Ge'Bv64'(src2, 256bv64)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shl'Bv256'(src1, 0bv192 ++ src2);
}

function $shrBv256From64(src1: bv256, src2: bv64) returns (bv256)
{
    $Shr'Bv256'(src1, 0bv192 ++ src2)
}

procedure {:inline 1} $ShrBv256From64(src1: bv256, src2: bv64) returns (dst: bv256)
{
    if ($Ge'Bv64'(src2, 256bv64)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shr'Bv256'(src1, 0bv192 ++ src2);
}

procedure {:inline 1} $CastBv128to256(src: bv128) returns (dst: bv256)
{
    dst := 0bv128 ++ src;
}


function $shlBv256From128(src1: bv256, src2: bv128) returns (bv256)
{
    $Shl'Bv256'(src1, 0bv128 ++ src2)
}

procedure {:inline 1} $ShlBv256From128(src1: bv256, src2: bv128) returns (dst: bv256)
{
    if ($Ge'Bv128'(src2, 256bv128)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shl'Bv256'(src1, 0bv128 ++ src2);
}

function $shrBv256From128(src1: bv256, src2: bv128) returns (bv256)
{
    $Shr'Bv256'(src1, 0bv128 ++ src2)
}

procedure {:inline 1} $ShrBv256From128(src1: bv256, src2: bv128) returns (dst: bv256)
{
    if ($Ge'Bv128'(src2, 256bv128)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shr'Bv256'(src1, 0bv128 ++ src2);
}

procedure {:inline 1} $CastBv256to256(src: bv256) returns (dst: bv256)
{
    dst := src;
}


function $shlBv256From256(src1: bv256, src2: bv256) returns (bv256)
{
    $Shl'Bv256'(src1, src2)
}

procedure {:inline 1} $ShlBv256From256(src1: bv256, src2: bv256) returns (dst: bv256)
{
    if ($Ge'Bv256'(src2, 256bv256)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shl'Bv256'(src1, src2);
}

function $shrBv256From256(src1: bv256, src2: bv256) returns (bv256)
{
    $Shr'Bv256'(src1, src2)
}

procedure {:inline 1} $ShrBv256From256(src1: bv256, src2: bv256) returns (dst: bv256)
{
    if ($Ge'Bv256'(src2, 256bv256)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shr'Bv256'(src1, src2);
}

procedure {:inline 1} $ShlU16(src1: int, src2: int) returns (dst: int)
{
    var res: int;
    // src2 is a u8
    assume src2 >= 0 && src2 < 256;
    if (src2 >= 16) {
        call $ExecFailureAbort();
        return;
    }
    dst := $shlU16(src1, src2);
}

procedure {:inline 1} $ShlU32(src1: int, src2: int) returns (dst: int)
{
    var res: int;
    // src2 is a u8
    assume src2 >= 0 && src2 < 256;
    if (src2 >= 32) {
        call $ExecFailureAbort();
        return;
    }
    dst := $shlU32(src1, src2);
}

procedure {:inline 1} $ShlU64(src1: int, src2: int) returns (dst: int)
{
    var res: int;
    // src2 is a u8
    assume src2 >= 0 && src2 < 256;
    if (src2 >= 64) {
       call $ExecFailureAbort();
       return;
    }
    dst := $shlU64(src1, src2);
}

procedure {:inline 1} $ShlU128(src1: int, src2: int) returns (dst: int)
{
    var res: int;
    // src2 is a u8
    assume src2 >= 0 && src2 < 256;
    if (src2 >= 128) {
        call $ExecFailureAbort();
        return;
    }
    dst := $shlU128(src1, src2);
}

procedure {:inline 1} $ShlU256(src1: int, src2: int) returns (dst: int)
{
    var res: int;
    // src2 is a u8
    assume src2 >= 0 && src2 < 256;
    dst := $shlU256(src1, src2);
}

procedure {:inline 1} $Shr(src1: int, src2: int) returns (dst: int)
{
    var res: int;
    // src2 is a u8
    assume src2 >= 0 && src2 < 256;
    dst := $shr(src1, src2);
}

procedure {:inline 1} $ShrU8(src1: int, src2: int) returns (dst: int)
{
    var res: int;
    // src2 is a u8
    assume src2 >= 0 && src2 < 256;
    if (src2 >= 8) {
        call $ExecFailureAbort();
        return;
    }
    dst := $shr(src1, src2);
}

procedure {:inline 1} $ShrU16(src1: int, src2: int) returns (dst: int)
{
    var res: int;
    // src2 is a u8
    assume src2 >= 0 && src2 < 256;
    if (src2 >= 16) {
        call $ExecFailureAbort();
        return;
    }
    dst := $shr(src1, src2);
}

procedure {:inline 1} $ShrU32(src1: int, src2: int) returns (dst: int)
{
    var res: int;
    // src2 is a u8
    assume src2 >= 0 && src2 < 256;
    if (src2 >= 32) {
        call $ExecFailureAbort();
        return;
    }
    dst := $shr(src1, src2);
}

procedure {:inline 1} $ShrU64(src1: int, src2: int) returns (dst: int)
{
    var res: int;
    // src2 is a u8
    assume src2 >= 0 && src2 < 256;
    if (src2 >= 64) {
        call $ExecFailureAbort();
        return;
    }
    dst := $shr(src1, src2);
}

procedure {:inline 1} $ShrU128(src1: int, src2: int) returns (dst: int)
{
    var res: int;
    // src2 is a u8
    assume src2 >= 0 && src2 < 256;
    if (src2 >= 128) {
        call $ExecFailureAbort();
        return;
    }
    dst := $shr(src1, src2);
}

procedure {:inline 1} $ShrU256(src1: int, src2: int) returns (dst: int)
{
    var res: int;
    // src2 is a u8
    assume src2 >= 0 && src2 < 256;
    dst := $shr(src1, src2);
}

procedure {:inline 1} $MulU8(src1: int, src2: int) returns (dst: int)
{
    if (src1 * src2 > $MAX_U8) {
        call $ExecFailureAbort();
        return;
    }
    dst := src1 * src2;
}

procedure {:inline 1} $MulU16(src1: int, src2: int) returns (dst: int)
{
    if (src1 * src2 > $MAX_U16) {
        call $ExecFailureAbort();
        return;
    }
    dst := src1 * src2;
}

procedure {:inline 1} $MulU32(src1: int, src2: int) returns (dst: int)
{
    if (src1 * src2 > $MAX_U32) {
        call $ExecFailureAbort();
        return;
    }
    dst := src1 * src2;
}

procedure {:inline 1} $MulU64(src1: int, src2: int) returns (dst: int)
{
    if (src1 * src2 > $MAX_U64) {
        call $ExecFailureAbort();
        return;
    }
    dst := src1 * src2;
}

procedure {:inline 1} $MulU128(src1: int, src2: int) returns (dst: int)
{
    if (src1 * src2 > $MAX_U128) {
        call $ExecFailureAbort();
        return;
    }
    dst := src1 * src2;
}

procedure {:inline 1} $MulU256(src1: int, src2: int) returns (dst: int)
{
    if (src1 * src2 > $MAX_U256) {
        call $ExecFailureAbort();
        return;
    }
    dst := src1 * src2;
}

procedure {:inline 1} $Div(src1: int, src2: int) returns (dst: int)
{
    if (src2 == 0) {
        call $ExecFailureAbort();
        return;
    }
    dst := src1 div src2;
}

procedure {:inline 1} $Mod(src1: int, src2: int) returns (dst: int)
{
    if (src2 == 0) {
        call $ExecFailureAbort();
        return;
    }
    dst := src1 mod src2;
}

procedure {:inline 1} $ArithBinaryUnimplemented(src1: int, src2: int) returns (dst: int);

procedure {:inline 1} $Lt(src1: int, src2: int) returns (dst: bool)
{
    dst := src1 < src2;
}

procedure {:inline 1} $Gt(src1: int, src2: int) returns (dst: bool)
{
    dst := src1 > src2;
}

procedure {:inline 1} $Le(src1: int, src2: int) returns (dst: bool)
{
    dst := src1 <= src2;
}

procedure {:inline 1} $Ge(src1: int, src2: int) returns (dst: bool)
{
    dst := src1 >= src2;
}

procedure {:inline 1} $And(src1: bool, src2: bool) returns (dst: bool)
{
    dst := src1 && src2;
}

procedure {:inline 1} $Or(src1: bool, src2: bool) returns (dst: bool)
{
    dst := src1 || src2;
}

procedure {:inline 1} $Not(src: bool) returns (dst: bool)
{
    dst := !src;
}

// Pack and Unpack are auto-generated for each type T


// ==================================================================================
// Native Vector

function {:inline} $SliceVecByRange<T>(v: Vec T, r: $Range): Vec T {
    SliceVec(v, lb#$Range(r), ub#$Range(r))
}

// ----------------------------------------------------------------------------------
// Native Vector implementation for element type `address`

// Not inlined. It appears faster this way.
function $IsEqual'vec'address''(v1: Vec (int), v2: Vec (int)): bool {
    LenVec(v1) == LenVec(v2) &&
    (forall i: int:: InRangeVec(v1, i) ==> $IsEqual'address'(ReadVec(v1, i), ReadVec(v2, i)))
}

// Not inlined.
function $IsPrefix'vec'address''(v: Vec (int), prefix: Vec (int)): bool {
    LenVec(v) >= LenVec(prefix) &&
    (forall i: int:: InRangeVec(prefix, i) ==> $IsEqual'address'(ReadVec(v, i), ReadVec(prefix, i)))
}

// Not inlined.
function $IsSuffix'vec'address''(v: Vec (int), suffix: Vec (int)): bool {
    LenVec(v) >= LenVec(suffix) &&
    (forall i: int:: InRangeVec(suffix, i) ==> $IsEqual'address'(ReadVec(v, LenVec(v) - LenVec(suffix) + i), ReadVec(suffix, i)))
}

// Not inlined.
function $IsValid'vec'address''(v: Vec (int)): bool {
    $IsValid'u64'(LenVec(v)) &&
    (forall i: int:: InRangeVec(v, i) ==> $IsValid'address'(ReadVec(v, i)))
}


function {:inline} $ContainsVec'address'(v: Vec (int), e: int): bool {
    (exists i: int :: $IsValid'u64'(i) && InRangeVec(v, i) && $IsEqual'address'(ReadVec(v, i), e))
}

function $IndexOfVec'address'(v: Vec (int), e: int): int;
axiom (forall v: Vec (int), e: int:: {$IndexOfVec'address'(v, e)}
    (var i := $IndexOfVec'address'(v, e);
     if (!$ContainsVec'address'(v, e)) then i == -1
     else $IsValid'u64'(i) && InRangeVec(v, i) && $IsEqual'address'(ReadVec(v, i), e) &&
        (forall j: int :: $IsValid'u64'(j) && j >= 0 && j < i ==> !$IsEqual'address'(ReadVec(v, j), e))));


function {:inline} $RangeVec'address'(v: Vec (int)): $Range {
    $Range(0, LenVec(v))
}


function {:inline} $EmptyVec'address'(): Vec (int) {
    EmptyVec()
}

procedure {:inline 1} $1_vector_empty'address'() returns (v: Vec (int)) {
    v := EmptyVec();
}

function {:inline} $1_vector_$empty'address'(): Vec (int) {
    EmptyVec()
}

procedure {:inline 1} $1_vector_is_empty'address'(v: Vec (int)) returns (b: bool) {
    b := IsEmptyVec(v);
}

procedure {:inline 1} $1_vector_push_back'address'(m: $Mutation (Vec (int)), val: int) returns (m': $Mutation (Vec (int))) {
    m' := $UpdateMutation(m, ExtendVec($Dereference(m), val));
}

function {:inline} $1_vector_$push_back'address'(v: Vec (int), val: int): Vec (int) {
    ExtendVec(v, val)
}

procedure {:inline 1} $1_vector_pop_back'address'(m: $Mutation (Vec (int))) returns (e: int, m': $Mutation (Vec (int))) {
    var v: Vec (int);
    var len: int;
    v := $Dereference(m);
    len := LenVec(v);
    if (len == 0) {
        call $ExecFailureAbort();
        return;
    }
    e := ReadVec(v, len-1);
    m' := $UpdateMutation(m, RemoveVec(v));
}

procedure {:inline 1} $1_vector_append'address'(m: $Mutation (Vec (int)), other: Vec (int)) returns (m': $Mutation (Vec (int))) {
    m' := $UpdateMutation(m, ConcatVec($Dereference(m), other));
}

procedure {:inline 1} $1_vector_reverse'address'(m: $Mutation (Vec (int))) returns (m': $Mutation (Vec (int))) {
    m' := $UpdateMutation(m, ReverseVec($Dereference(m)));
}

procedure {:inline 1} $1_vector_reverse_append'address'(m: $Mutation (Vec (int)), other: Vec (int)) returns (m': $Mutation (Vec (int))) {
    m' := $UpdateMutation(m, ConcatVec($Dereference(m), ReverseVec(other)));
}

procedure {:inline 1} $1_vector_trim_reverse'address'(m: $Mutation (Vec (int)), new_len: int) returns (v: (Vec (int)), m': $Mutation (Vec (int))) {
    var len: int;
    v := $Dereference(m);
    if (LenVec(v) < new_len) {
        call $ExecFailureAbort();
        return;
    }
    v := SliceVec(v, new_len, LenVec(v));
    v := ReverseVec(v);
    m' := $UpdateMutation(m, SliceVec($Dereference(m), 0, new_len));
}

procedure {:inline 1} $1_vector_trim'address'(m: $Mutation (Vec (int)), new_len: int) returns (v: (Vec (int)), m': $Mutation (Vec (int))) {
    var len: int;
    v := $Dereference(m);
    if (LenVec(v) < new_len) {
        call $ExecFailureAbort();
        return;
    }
    v := SliceVec(v, new_len, LenVec(v));
    m' := $UpdateMutation(m, SliceVec($Dereference(m), 0, new_len));
}

procedure {:inline 1} $1_vector_reverse_slice'address'(m: $Mutation (Vec (int)), left: int, right: int) returns (m': $Mutation (Vec (int))) {
    var left_vec: Vec (int);
    var mid_vec: Vec (int);
    var right_vec: Vec (int);
    var v: Vec (int);
    if (left > right) {
        call $ExecFailureAbort();
        return;
    }
    if (left == right) {
        m' := m;
        return;
    }
    v := $Dereference(m);
    if (!(right >= 0 && right <= LenVec(v))) {
        call $ExecFailureAbort();
        return;
    }
    left_vec := SliceVec(v, 0, left);
    right_vec := SliceVec(v, right, LenVec(v));
    mid_vec := ReverseVec(SliceVec(v, left, right));
    m' := $UpdateMutation(m, ConcatVec(left_vec, ConcatVec(mid_vec, right_vec)));
}

procedure {:inline 1} $1_vector_rotate'address'(m: $Mutation (Vec (int)), rot: int) returns (n: int, m': $Mutation (Vec (int))) {
    var v: Vec (int);
    var len: int;
    var left_vec: Vec (int);
    var right_vec: Vec (int);
    v := $Dereference(m);
    if (!(rot >= 0 && rot <= LenVec(v))) {
        call $ExecFailureAbort();
        return;
    }
    left_vec := SliceVec(v, 0, rot);
    right_vec := SliceVec(v, rot, LenVec(v));
    m' := $UpdateMutation(m, ConcatVec(right_vec, left_vec));
    n := LenVec(v) - rot;
}

procedure {:inline 1} $1_vector_rotate_slice'address'(m: $Mutation (Vec (int)), left: int, rot: int, right: int) returns (n: int, m': $Mutation (Vec (int))) {
    var left_vec: Vec (int);
    var mid_vec: Vec (int);
    var right_vec: Vec (int);
    var mid_left_vec: Vec (int);
    var mid_right_vec: Vec (int);
    var v: Vec (int);
    v := $Dereference(m);
    if (!(left <= rot && rot <= right)) {
        call $ExecFailureAbort();
        return;
    }
    if (!(right >= 0 && right <= LenVec(v))) {
        call $ExecFailureAbort();
        return;
    }
    v := $Dereference(m);
    left_vec := SliceVec(v, 0, left);
    right_vec := SliceVec(v, right, LenVec(v));
    mid_left_vec := SliceVec(v, left, rot);
    mid_right_vec := SliceVec(v, rot, right);
    mid_vec := ConcatVec(mid_right_vec, mid_left_vec);
    m' := $UpdateMutation(m, ConcatVec(left_vec, ConcatVec(mid_vec, right_vec)));
    n := left + (right - rot);
}

procedure {:inline 1} $1_vector_insert'address'(m: $Mutation (Vec (int)), i: int, e: int) returns (m': $Mutation (Vec (int))) {
    var left_vec: Vec (int);
    var right_vec: Vec (int);
    var v: Vec (int);
    v := $Dereference(m);
    if (!(i >= 0 && i <= LenVec(v))) {
        call $ExecFailureAbort();
        return;
    }
    if (i == LenVec(v)) {
        m' := $UpdateMutation(m, ExtendVec(v, e));
    } else {
        left_vec := ExtendVec(SliceVec(v, 0, i), e);
        right_vec := SliceVec(v, i, LenVec(v));
        m' := $UpdateMutation(m, ConcatVec(left_vec, right_vec));
    }
}

procedure {:inline 1} $1_vector_length'address'(v: Vec (int)) returns (l: int) {
    l := LenVec(v);
}

function {:inline} $1_vector_$length'address'(v: Vec (int)): int {
    LenVec(v)
}

procedure {:inline 1} $1_vector_borrow'address'(v: Vec (int), i: int) returns (dst: int) {
    if (!InRangeVec(v, i)) {
        call $ExecFailureAbort();
        return;
    }
    dst := ReadVec(v, i);
}

function {:inline} $1_vector_$borrow'address'(v: Vec (int), i: int): int {
    ReadVec(v, i)
}

procedure {:inline 1} $1_vector_borrow_mut'address'(m: $Mutation (Vec (int)), index: int)
returns (dst: $Mutation (int), m': $Mutation (Vec (int)))
{
    var v: Vec (int);
    v := $Dereference(m);
    if (!InRangeVec(v, index)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Mutation(l#$Mutation(m), ExtendVec(p#$Mutation(m), index), ReadVec(v, index));
    m' := m;
}

function {:inline} $1_vector_$borrow_mut'address'(v: Vec (int), i: int): int {
    ReadVec(v, i)
}

procedure {:inline 1} $1_vector_destroy_empty'address'(v: Vec (int)) {
    if (!IsEmptyVec(v)) {
      call $ExecFailureAbort();
    }
}

procedure {:inline 1} $1_vector_swap'address'(m: $Mutation (Vec (int)), i: int, j: int) returns (m': $Mutation (Vec (int)))
{
    var v: Vec (int);
    v := $Dereference(m);
    if (!InRangeVec(v, i) || !InRangeVec(v, j)) {
        call $ExecFailureAbort();
        return;
    }
    m' := $UpdateMutation(m, SwapVec(v, i, j));
}

function {:inline} $1_vector_$swap'address'(v: Vec (int), i: int, j: int): Vec (int) {
    SwapVec(v, i, j)
}

procedure {:inline 1} $1_vector_remove'address'(m: $Mutation (Vec (int)), i: int) returns (e: int, m': $Mutation (Vec (int)))
{
    var v: Vec (int);

    v := $Dereference(m);

    if (!InRangeVec(v, i)) {
        call $ExecFailureAbort();
        return;
    }
    e := ReadVec(v, i);
    m' := $UpdateMutation(m, RemoveAtVec(v, i));
}

procedure {:inline 1} $1_vector_swap_remove'address'(m: $Mutation (Vec (int)), i: int) returns (e: int, m': $Mutation (Vec (int)))
{
    var len: int;
    var v: Vec (int);

    v := $Dereference(m);
    len := LenVec(v);
    if (!InRangeVec(v, i)) {
        call $ExecFailureAbort();
        return;
    }
    e := ReadVec(v, i);
    m' := $UpdateMutation(m, RemoveVec(SwapVec(v, i, len-1)));
}

procedure {:inline 1} $1_vector_contains'address'(v: Vec (int), e: int) returns (res: bool)  {
    res := $ContainsVec'address'(v, e);
}

procedure {:inline 1}
$1_vector_index_of'address'(v: Vec (int), e: int) returns (res1: bool, res2: int) {
    res2 := $IndexOfVec'address'(v, e);
    if (res2 >= 0) {
        res1 := true;
    } else {
        res1 := false;
        res2 := 0;
    }
}


// ----------------------------------------------------------------------------------
// Native Vector implementation for element type `u8`

// Not inlined. It appears faster this way.
function $IsEqual'vec'u8''(v1: Vec (int), v2: Vec (int)): bool {
    LenVec(v1) == LenVec(v2) &&
    (forall i: int:: InRangeVec(v1, i) ==> $IsEqual'u8'(ReadVec(v1, i), ReadVec(v2, i)))
}

// Not inlined.
function $IsPrefix'vec'u8''(v: Vec (int), prefix: Vec (int)): bool {
    LenVec(v) >= LenVec(prefix) &&
    (forall i: int:: InRangeVec(prefix, i) ==> $IsEqual'u8'(ReadVec(v, i), ReadVec(prefix, i)))
}

// Not inlined.
function $IsSuffix'vec'u8''(v: Vec (int), suffix: Vec (int)): bool {
    LenVec(v) >= LenVec(suffix) &&
    (forall i: int:: InRangeVec(suffix, i) ==> $IsEqual'u8'(ReadVec(v, LenVec(v) - LenVec(suffix) + i), ReadVec(suffix, i)))
}

// Not inlined.
function $IsValid'vec'u8''(v: Vec (int)): bool {
    $IsValid'u64'(LenVec(v)) &&
    (forall i: int:: InRangeVec(v, i) ==> $IsValid'u8'(ReadVec(v, i)))
}


function {:inline} $ContainsVec'u8'(v: Vec (int), e: int): bool {
    (exists i: int :: $IsValid'u64'(i) && InRangeVec(v, i) && $IsEqual'u8'(ReadVec(v, i), e))
}

function $IndexOfVec'u8'(v: Vec (int), e: int): int;
axiom (forall v: Vec (int), e: int:: {$IndexOfVec'u8'(v, e)}
    (var i := $IndexOfVec'u8'(v, e);
     if (!$ContainsVec'u8'(v, e)) then i == -1
     else $IsValid'u64'(i) && InRangeVec(v, i) && $IsEqual'u8'(ReadVec(v, i), e) &&
        (forall j: int :: $IsValid'u64'(j) && j >= 0 && j < i ==> !$IsEqual'u8'(ReadVec(v, j), e))));


function {:inline} $RangeVec'u8'(v: Vec (int)): $Range {
    $Range(0, LenVec(v))
}


function {:inline} $EmptyVec'u8'(): Vec (int) {
    EmptyVec()
}

procedure {:inline 1} $1_vector_empty'u8'() returns (v: Vec (int)) {
    v := EmptyVec();
}

function {:inline} $1_vector_$empty'u8'(): Vec (int) {
    EmptyVec()
}

procedure {:inline 1} $1_vector_is_empty'u8'(v: Vec (int)) returns (b: bool) {
    b := IsEmptyVec(v);
}

procedure {:inline 1} $1_vector_push_back'u8'(m: $Mutation (Vec (int)), val: int) returns (m': $Mutation (Vec (int))) {
    m' := $UpdateMutation(m, ExtendVec($Dereference(m), val));
}

function {:inline} $1_vector_$push_back'u8'(v: Vec (int), val: int): Vec (int) {
    ExtendVec(v, val)
}

procedure {:inline 1} $1_vector_pop_back'u8'(m: $Mutation (Vec (int))) returns (e: int, m': $Mutation (Vec (int))) {
    var v: Vec (int);
    var len: int;
    v := $Dereference(m);
    len := LenVec(v);
    if (len == 0) {
        call $ExecFailureAbort();
        return;
    }
    e := ReadVec(v, len-1);
    m' := $UpdateMutation(m, RemoveVec(v));
}

procedure {:inline 1} $1_vector_append'u8'(m: $Mutation (Vec (int)), other: Vec (int)) returns (m': $Mutation (Vec (int))) {
    m' := $UpdateMutation(m, ConcatVec($Dereference(m), other));
}

procedure {:inline 1} $1_vector_reverse'u8'(m: $Mutation (Vec (int))) returns (m': $Mutation (Vec (int))) {
    m' := $UpdateMutation(m, ReverseVec($Dereference(m)));
}

procedure {:inline 1} $1_vector_reverse_append'u8'(m: $Mutation (Vec (int)), other: Vec (int)) returns (m': $Mutation (Vec (int))) {
    m' := $UpdateMutation(m, ConcatVec($Dereference(m), ReverseVec(other)));
}

procedure {:inline 1} $1_vector_trim_reverse'u8'(m: $Mutation (Vec (int)), new_len: int) returns (v: (Vec (int)), m': $Mutation (Vec (int))) {
    var len: int;
    v := $Dereference(m);
    if (LenVec(v) < new_len) {
        call $ExecFailureAbort();
        return;
    }
    v := SliceVec(v, new_len, LenVec(v));
    v := ReverseVec(v);
    m' := $UpdateMutation(m, SliceVec($Dereference(m), 0, new_len));
}

procedure {:inline 1} $1_vector_trim'u8'(m: $Mutation (Vec (int)), new_len: int) returns (v: (Vec (int)), m': $Mutation (Vec (int))) {
    var len: int;
    v := $Dereference(m);
    if (LenVec(v) < new_len) {
        call $ExecFailureAbort();
        return;
    }
    v := SliceVec(v, new_len, LenVec(v));
    m' := $UpdateMutation(m, SliceVec($Dereference(m), 0, new_len));
}

procedure {:inline 1} $1_vector_reverse_slice'u8'(m: $Mutation (Vec (int)), left: int, right: int) returns (m': $Mutation (Vec (int))) {
    var left_vec: Vec (int);
    var mid_vec: Vec (int);
    var right_vec: Vec (int);
    var v: Vec (int);
    if (left > right) {
        call $ExecFailureAbort();
        return;
    }
    if (left == right) {
        m' := m;
        return;
    }
    v := $Dereference(m);
    if (!(right >= 0 && right <= LenVec(v))) {
        call $ExecFailureAbort();
        return;
    }
    left_vec := SliceVec(v, 0, left);
    right_vec := SliceVec(v, right, LenVec(v));
    mid_vec := ReverseVec(SliceVec(v, left, right));
    m' := $UpdateMutation(m, ConcatVec(left_vec, ConcatVec(mid_vec, right_vec)));
}

procedure {:inline 1} $1_vector_rotate'u8'(m: $Mutation (Vec (int)), rot: int) returns (n: int, m': $Mutation (Vec (int))) {
    var v: Vec (int);
    var len: int;
    var left_vec: Vec (int);
    var right_vec: Vec (int);
    v := $Dereference(m);
    if (!(rot >= 0 && rot <= LenVec(v))) {
        call $ExecFailureAbort();
        return;
    }
    left_vec := SliceVec(v, 0, rot);
    right_vec := SliceVec(v, rot, LenVec(v));
    m' := $UpdateMutation(m, ConcatVec(right_vec, left_vec));
    n := LenVec(v) - rot;
}

procedure {:inline 1} $1_vector_rotate_slice'u8'(m: $Mutation (Vec (int)), left: int, rot: int, right: int) returns (n: int, m': $Mutation (Vec (int))) {
    var left_vec: Vec (int);
    var mid_vec: Vec (int);
    var right_vec: Vec (int);
    var mid_left_vec: Vec (int);
    var mid_right_vec: Vec (int);
    var v: Vec (int);
    v := $Dereference(m);
    if (!(left <= rot && rot <= right)) {
        call $ExecFailureAbort();
        return;
    }
    if (!(right >= 0 && right <= LenVec(v))) {
        call $ExecFailureAbort();
        return;
    }
    v := $Dereference(m);
    left_vec := SliceVec(v, 0, left);
    right_vec := SliceVec(v, right, LenVec(v));
    mid_left_vec := SliceVec(v, left, rot);
    mid_right_vec := SliceVec(v, rot, right);
    mid_vec := ConcatVec(mid_right_vec, mid_left_vec);
    m' := $UpdateMutation(m, ConcatVec(left_vec, ConcatVec(mid_vec, right_vec)));
    n := left + (right - rot);
}

procedure {:inline 1} $1_vector_insert'u8'(m: $Mutation (Vec (int)), i: int, e: int) returns (m': $Mutation (Vec (int))) {
    var left_vec: Vec (int);
    var right_vec: Vec (int);
    var v: Vec (int);
    v := $Dereference(m);
    if (!(i >= 0 && i <= LenVec(v))) {
        call $ExecFailureAbort();
        return;
    }
    if (i == LenVec(v)) {
        m' := $UpdateMutation(m, ExtendVec(v, e));
    } else {
        left_vec := ExtendVec(SliceVec(v, 0, i), e);
        right_vec := SliceVec(v, i, LenVec(v));
        m' := $UpdateMutation(m, ConcatVec(left_vec, right_vec));
    }
}

procedure {:inline 1} $1_vector_length'u8'(v: Vec (int)) returns (l: int) {
    l := LenVec(v);
}

function {:inline} $1_vector_$length'u8'(v: Vec (int)): int {
    LenVec(v)
}

procedure {:inline 1} $1_vector_borrow'u8'(v: Vec (int), i: int) returns (dst: int) {
    if (!InRangeVec(v, i)) {
        call $ExecFailureAbort();
        return;
    }
    dst := ReadVec(v, i);
}

function {:inline} $1_vector_$borrow'u8'(v: Vec (int), i: int): int {
    ReadVec(v, i)
}

procedure {:inline 1} $1_vector_borrow_mut'u8'(m: $Mutation (Vec (int)), index: int)
returns (dst: $Mutation (int), m': $Mutation (Vec (int)))
{
    var v: Vec (int);
    v := $Dereference(m);
    if (!InRangeVec(v, index)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Mutation(l#$Mutation(m), ExtendVec(p#$Mutation(m), index), ReadVec(v, index));
    m' := m;
}

function {:inline} $1_vector_$borrow_mut'u8'(v: Vec (int), i: int): int {
    ReadVec(v, i)
}

procedure {:inline 1} $1_vector_destroy_empty'u8'(v: Vec (int)) {
    if (!IsEmptyVec(v)) {
      call $ExecFailureAbort();
    }
}

procedure {:inline 1} $1_vector_swap'u8'(m: $Mutation (Vec (int)), i: int, j: int) returns (m': $Mutation (Vec (int)))
{
    var v: Vec (int);
    v := $Dereference(m);
    if (!InRangeVec(v, i) || !InRangeVec(v, j)) {
        call $ExecFailureAbort();
        return;
    }
    m' := $UpdateMutation(m, SwapVec(v, i, j));
}

function {:inline} $1_vector_$swap'u8'(v: Vec (int), i: int, j: int): Vec (int) {
    SwapVec(v, i, j)
}

procedure {:inline 1} $1_vector_remove'u8'(m: $Mutation (Vec (int)), i: int) returns (e: int, m': $Mutation (Vec (int)))
{
    var v: Vec (int);

    v := $Dereference(m);

    if (!InRangeVec(v, i)) {
        call $ExecFailureAbort();
        return;
    }
    e := ReadVec(v, i);
    m' := $UpdateMutation(m, RemoveAtVec(v, i));
}

procedure {:inline 1} $1_vector_swap_remove'u8'(m: $Mutation (Vec (int)), i: int) returns (e: int, m': $Mutation (Vec (int)))
{
    var len: int;
    var v: Vec (int);

    v := $Dereference(m);
    len := LenVec(v);
    if (!InRangeVec(v, i)) {
        call $ExecFailureAbort();
        return;
    }
    e := ReadVec(v, i);
    m' := $UpdateMutation(m, RemoveVec(SwapVec(v, i, len-1)));
}

procedure {:inline 1} $1_vector_contains'u8'(v: Vec (int), e: int) returns (res: bool)  {
    res := $ContainsVec'u8'(v, e);
}

procedure {:inline 1}
$1_vector_index_of'u8'(v: Vec (int), e: int) returns (res1: bool, res2: int) {
    res2 := $IndexOfVec'u8'(v, e);
    if (res2 >= 0) {
        res1 := true;
    } else {
        res1 := false;
        res2 := 0;
    }
}


// ----------------------------------------------------------------------------------
// Native Vector implementation for element type `bv8`

// Not inlined. It appears faster this way.
function $IsEqual'vec'bv8''(v1: Vec (bv8), v2: Vec (bv8)): bool {
    LenVec(v1) == LenVec(v2) &&
    (forall i: int:: InRangeVec(v1, i) ==> $IsEqual'bv8'(ReadVec(v1, i), ReadVec(v2, i)))
}

// Not inlined.
function $IsPrefix'vec'bv8''(v: Vec (bv8), prefix: Vec (bv8)): bool {
    LenVec(v) >= LenVec(prefix) &&
    (forall i: int:: InRangeVec(prefix, i) ==> $IsEqual'bv8'(ReadVec(v, i), ReadVec(prefix, i)))
}

// Not inlined.
function $IsSuffix'vec'bv8''(v: Vec (bv8), suffix: Vec (bv8)): bool {
    LenVec(v) >= LenVec(suffix) &&
    (forall i: int:: InRangeVec(suffix, i) ==> $IsEqual'bv8'(ReadVec(v, LenVec(v) - LenVec(suffix) + i), ReadVec(suffix, i)))
}

// Not inlined.
function $IsValid'vec'bv8''(v: Vec (bv8)): bool {
    $IsValid'u64'(LenVec(v)) &&
    (forall i: int:: InRangeVec(v, i) ==> $IsValid'bv8'(ReadVec(v, i)))
}


function {:inline} $ContainsVec'bv8'(v: Vec (bv8), e: bv8): bool {
    (exists i: int :: $IsValid'u64'(i) && InRangeVec(v, i) && $IsEqual'bv8'(ReadVec(v, i), e))
}

function $IndexOfVec'bv8'(v: Vec (bv8), e: bv8): int;
axiom (forall v: Vec (bv8), e: bv8:: {$IndexOfVec'bv8'(v, e)}
    (var i := $IndexOfVec'bv8'(v, e);
     if (!$ContainsVec'bv8'(v, e)) then i == -1
     else $IsValid'u64'(i) && InRangeVec(v, i) && $IsEqual'bv8'(ReadVec(v, i), e) &&
        (forall j: int :: $IsValid'u64'(j) && j >= 0 && j < i ==> !$IsEqual'bv8'(ReadVec(v, j), e))));


function {:inline} $RangeVec'bv8'(v: Vec (bv8)): $Range {
    $Range(0, LenVec(v))
}


function {:inline} $EmptyVec'bv8'(): Vec (bv8) {
    EmptyVec()
}

procedure {:inline 1} $1_vector_empty'bv8'() returns (v: Vec (bv8)) {
    v := EmptyVec();
}

function {:inline} $1_vector_$empty'bv8'(): Vec (bv8) {
    EmptyVec()
}

procedure {:inline 1} $1_vector_is_empty'bv8'(v: Vec (bv8)) returns (b: bool) {
    b := IsEmptyVec(v);
}

procedure {:inline 1} $1_vector_push_back'bv8'(m: $Mutation (Vec (bv8)), val: bv8) returns (m': $Mutation (Vec (bv8))) {
    m' := $UpdateMutation(m, ExtendVec($Dereference(m), val));
}

function {:inline} $1_vector_$push_back'bv8'(v: Vec (bv8), val: bv8): Vec (bv8) {
    ExtendVec(v, val)
}

procedure {:inline 1} $1_vector_pop_back'bv8'(m: $Mutation (Vec (bv8))) returns (e: bv8, m': $Mutation (Vec (bv8))) {
    var v: Vec (bv8);
    var len: int;
    v := $Dereference(m);
    len := LenVec(v);
    if (len == 0) {
        call $ExecFailureAbort();
        return;
    }
    e := ReadVec(v, len-1);
    m' := $UpdateMutation(m, RemoveVec(v));
}

procedure {:inline 1} $1_vector_append'bv8'(m: $Mutation (Vec (bv8)), other: Vec (bv8)) returns (m': $Mutation (Vec (bv8))) {
    m' := $UpdateMutation(m, ConcatVec($Dereference(m), other));
}

procedure {:inline 1} $1_vector_reverse'bv8'(m: $Mutation (Vec (bv8))) returns (m': $Mutation (Vec (bv8))) {
    m' := $UpdateMutation(m, ReverseVec($Dereference(m)));
}

procedure {:inline 1} $1_vector_reverse_append'bv8'(m: $Mutation (Vec (bv8)), other: Vec (bv8)) returns (m': $Mutation (Vec (bv8))) {
    m' := $UpdateMutation(m, ConcatVec($Dereference(m), ReverseVec(other)));
}

procedure {:inline 1} $1_vector_trim_reverse'bv8'(m: $Mutation (Vec (bv8)), new_len: int) returns (v: (Vec (bv8)), m': $Mutation (Vec (bv8))) {
    var len: int;
    v := $Dereference(m);
    if (LenVec(v) < new_len) {
        call $ExecFailureAbort();
        return;
    }
    v := SliceVec(v, new_len, LenVec(v));
    v := ReverseVec(v);
    m' := $UpdateMutation(m, SliceVec($Dereference(m), 0, new_len));
}

procedure {:inline 1} $1_vector_trim'bv8'(m: $Mutation (Vec (bv8)), new_len: int) returns (v: (Vec (bv8)), m': $Mutation (Vec (bv8))) {
    var len: int;
    v := $Dereference(m);
    if (LenVec(v) < new_len) {
        call $ExecFailureAbort();
        return;
    }
    v := SliceVec(v, new_len, LenVec(v));
    m' := $UpdateMutation(m, SliceVec($Dereference(m), 0, new_len));
}

procedure {:inline 1} $1_vector_reverse_slice'bv8'(m: $Mutation (Vec (bv8)), left: int, right: int) returns (m': $Mutation (Vec (bv8))) {
    var left_vec: Vec (bv8);
    var mid_vec: Vec (bv8);
    var right_vec: Vec (bv8);
    var v: Vec (bv8);
    if (left > right) {
        call $ExecFailureAbort();
        return;
    }
    if (left == right) {
        m' := m;
        return;
    }
    v := $Dereference(m);
    if (!(right >= 0 && right <= LenVec(v))) {
        call $ExecFailureAbort();
        return;
    }
    left_vec := SliceVec(v, 0, left);
    right_vec := SliceVec(v, right, LenVec(v));
    mid_vec := ReverseVec(SliceVec(v, left, right));
    m' := $UpdateMutation(m, ConcatVec(left_vec, ConcatVec(mid_vec, right_vec)));
}

procedure {:inline 1} $1_vector_rotate'bv8'(m: $Mutation (Vec (bv8)), rot: int) returns (n: int, m': $Mutation (Vec (bv8))) {
    var v: Vec (bv8);
    var len: int;
    var left_vec: Vec (bv8);
    var right_vec: Vec (bv8);
    v := $Dereference(m);
    if (!(rot >= 0 && rot <= LenVec(v))) {
        call $ExecFailureAbort();
        return;
    }
    left_vec := SliceVec(v, 0, rot);
    right_vec := SliceVec(v, rot, LenVec(v));
    m' := $UpdateMutation(m, ConcatVec(right_vec, left_vec));
    n := LenVec(v) - rot;
}

procedure {:inline 1} $1_vector_rotate_slice'bv8'(m: $Mutation (Vec (bv8)), left: int, rot: int, right: int) returns (n: int, m': $Mutation (Vec (bv8))) {
    var left_vec: Vec (bv8);
    var mid_vec: Vec (bv8);
    var right_vec: Vec (bv8);
    var mid_left_vec: Vec (bv8);
    var mid_right_vec: Vec (bv8);
    var v: Vec (bv8);
    v := $Dereference(m);
    if (!(left <= rot && rot <= right)) {
        call $ExecFailureAbort();
        return;
    }
    if (!(right >= 0 && right <= LenVec(v))) {
        call $ExecFailureAbort();
        return;
    }
    v := $Dereference(m);
    left_vec := SliceVec(v, 0, left);
    right_vec := SliceVec(v, right, LenVec(v));
    mid_left_vec := SliceVec(v, left, rot);
    mid_right_vec := SliceVec(v, rot, right);
    mid_vec := ConcatVec(mid_right_vec, mid_left_vec);
    m' := $UpdateMutation(m, ConcatVec(left_vec, ConcatVec(mid_vec, right_vec)));
    n := left + (right - rot);
}

procedure {:inline 1} $1_vector_insert'bv8'(m: $Mutation (Vec (bv8)), i: int, e: bv8) returns (m': $Mutation (Vec (bv8))) {
    var left_vec: Vec (bv8);
    var right_vec: Vec (bv8);
    var v: Vec (bv8);
    v := $Dereference(m);
    if (!(i >= 0 && i <= LenVec(v))) {
        call $ExecFailureAbort();
        return;
    }
    if (i == LenVec(v)) {
        m' := $UpdateMutation(m, ExtendVec(v, e));
    } else {
        left_vec := ExtendVec(SliceVec(v, 0, i), e);
        right_vec := SliceVec(v, i, LenVec(v));
        m' := $UpdateMutation(m, ConcatVec(left_vec, right_vec));
    }
}

procedure {:inline 1} $1_vector_length'bv8'(v: Vec (bv8)) returns (l: int) {
    l := LenVec(v);
}

function {:inline} $1_vector_$length'bv8'(v: Vec (bv8)): int {
    LenVec(v)
}

procedure {:inline 1} $1_vector_borrow'bv8'(v: Vec (bv8), i: int) returns (dst: bv8) {
    if (!InRangeVec(v, i)) {
        call $ExecFailureAbort();
        return;
    }
    dst := ReadVec(v, i);
}

function {:inline} $1_vector_$borrow'bv8'(v: Vec (bv8), i: int): bv8 {
    ReadVec(v, i)
}

procedure {:inline 1} $1_vector_borrow_mut'bv8'(m: $Mutation (Vec (bv8)), index: int)
returns (dst: $Mutation (bv8), m': $Mutation (Vec (bv8)))
{
    var v: Vec (bv8);
    v := $Dereference(m);
    if (!InRangeVec(v, index)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Mutation(l#$Mutation(m), ExtendVec(p#$Mutation(m), index), ReadVec(v, index));
    m' := m;
}

function {:inline} $1_vector_$borrow_mut'bv8'(v: Vec (bv8), i: int): bv8 {
    ReadVec(v, i)
}

procedure {:inline 1} $1_vector_destroy_empty'bv8'(v: Vec (bv8)) {
    if (!IsEmptyVec(v)) {
      call $ExecFailureAbort();
    }
}

procedure {:inline 1} $1_vector_swap'bv8'(m: $Mutation (Vec (bv8)), i: int, j: int) returns (m': $Mutation (Vec (bv8)))
{
    var v: Vec (bv8);
    v := $Dereference(m);
    if (!InRangeVec(v, i) || !InRangeVec(v, j)) {
        call $ExecFailureAbort();
        return;
    }
    m' := $UpdateMutation(m, SwapVec(v, i, j));
}

function {:inline} $1_vector_$swap'bv8'(v: Vec (bv8), i: int, j: int): Vec (bv8) {
    SwapVec(v, i, j)
}

procedure {:inline 1} $1_vector_remove'bv8'(m: $Mutation (Vec (bv8)), i: int) returns (e: bv8, m': $Mutation (Vec (bv8)))
{
    var v: Vec (bv8);

    v := $Dereference(m);

    if (!InRangeVec(v, i)) {
        call $ExecFailureAbort();
        return;
    }
    e := ReadVec(v, i);
    m' := $UpdateMutation(m, RemoveAtVec(v, i));
}

procedure {:inline 1} $1_vector_swap_remove'bv8'(m: $Mutation (Vec (bv8)), i: int) returns (e: bv8, m': $Mutation (Vec (bv8)))
{
    var len: int;
    var v: Vec (bv8);

    v := $Dereference(m);
    len := LenVec(v);
    if (!InRangeVec(v, i)) {
        call $ExecFailureAbort();
        return;
    }
    e := ReadVec(v, i);
    m' := $UpdateMutation(m, RemoveVec(SwapVec(v, i, len-1)));
}

procedure {:inline 1} $1_vector_contains'bv8'(v: Vec (bv8), e: bv8) returns (res: bool)  {
    res := $ContainsVec'bv8'(v, e);
}

procedure {:inline 1}
$1_vector_index_of'bv8'(v: Vec (bv8), e: bv8) returns (res1: bool, res2: int) {
    res2 := $IndexOfVec'bv8'(v, e);
    if (res2 >= 0) {
        res1 := true;
    } else {
        res1 := false;
        res2 := 0;
    }
}


// ==================================================================================
// Native Table

// ----------------------------------------------------------------------------------
// Native Table key encoding for type `address`

function $EncodeKey'address'(k: int): int;
axiom (
  forall k1, k2: int :: {$EncodeKey'address'(k1), $EncodeKey'address'(k2)}
    $IsEqual'address'(k1, k2) <==> $EncodeKey'address'(k1) == $EncodeKey'address'(k2)
);


// ----------------------------------------------------------------------------------
// Native Table implementation for type `(address,u64)`

function $IsEqual'$1_simple_map_SimpleMap'address_u64''(t1: Table int (int), t2: Table int (int)): bool {
    LenTable(t1) == LenTable(t2) &&
    (forall k: int :: ContainsTable(t1, k) <==> ContainsTable(t2, k)) &&
    (forall k: int :: ContainsTable(t1, k) ==> GetTable(t1, k) == GetTable(t2, k)) &&
    (forall k: int :: ContainsTable(t2, k) ==> GetTable(t1, k) == GetTable(t2, k))
}

// Not inlined.
function $IsValid'$1_simple_map_SimpleMap'address_u64''(t: Table int (int)): bool {
    $IsValid'u64'(LenTable(t)) &&
    (forall i: int:: ContainsTable(t, i) ==> $IsValid'u64'(GetTable(t, i)))
}
procedure {:inline 2} $1_simple_map_create'address_u64'() returns (v: Table int (int)) {
    v := EmptyTable();
}
procedure {:inline 2} $1_simple_map_destroy_empty'address_u64'(t: Table int (int)) {
    if (LenTable(t) != 0) {
        call $Abort($StdError(1/*INVALID_STATE*/, 102/*ENOT_EMPTY*/));
    }
}
procedure {:inline 2} $1_simple_map_length'address_u64'(t: (Table int (int))) returns (l: int) {
    l := LenTable(t);
}
procedure {:inline 2} $1_simple_map_contains_key'address_u64'(t: (Table int (int)), k: int) returns (r: bool) {
    r := ContainsTable(t, $EncodeKey'address'(k));
}
procedure {:inline 2} $1_simple_map_add'address_u64'(m: $Mutation (Table int (int)), k: int, v: int) returns (m': $Mutation(Table int (int))) {
    var enc_k: int;
    var t: Table int (int);
    enc_k := $EncodeKey'address'(k);
    t := $Dereference(m);
    if (ContainsTable(t, enc_k)) {
        call $Abort($StdError(7/*INVALID_ARGUMENTS*/, 100/*EALREADY_EXISTS*/));
    } else {
        m' := $UpdateMutation(m, AddTable(t, enc_k, v));
    }
}
procedure {:inline 2} $1_simple_map_remove'address_u64'(m: $Mutation (Table int (int)), k: int)
returns (k': int, v: int, m': $Mutation(Table int (int))) {
    var enc_k: int;
    var t: Table int (int);
    enc_k := $EncodeKey'address'(k);
    t := $Dereference(m);
    if (!ContainsTable(t, enc_k)) {
        call $Abort($StdError(7/*INVALID_ARGUMENTS*/, 101/*ENOT_FOUND*/));
    } else {
        k' := k;
        v := GetTable(t, enc_k);
        m' := $UpdateMutation(m, RemoveTable(t, enc_k));
    }
}
procedure {:inline 2} $1_simple_map_borrow'address_u64'(t: Table int (int), k: int) returns (v: int) {
    var enc_k: int;
    enc_k := $EncodeKey'address'(k);
    if (!ContainsTable(t, enc_k)) {
        call $Abort($StdError(7/*INVALID_ARGUMENTS*/, 101/*ENOT_FOUND*/));
    } else {
        v := GetTable(t, $EncodeKey'address'(k));
    }
}
procedure {:inline 2} $1_simple_map_borrow_mut'address_u64'(m: $Mutation (Table int (int)), k: int)
returns (dst: $Mutation (int), m': $Mutation (Table int (int))) {
    var enc_k: int;
    var t: Table int (int);
    enc_k := $EncodeKey'address'(k);
    t := $Dereference(m);
    if (!ContainsTable(t, enc_k)) {
        call $Abort($StdError(7/*INVALID_ARGUMENTS*/, 101/*ENOT_FOUND*/));
    } else {
        dst := $Mutation(l#$Mutation(m), ExtendVec(p#$Mutation(m), enc_k), GetTable(t, enc_k));
        m' := m;
    }
}
function {:inline} $1_simple_map_spec_len'address_u64'(t: (Table int (int))): int {
    LenTable(t)
}
function {:inline} $1_simple_map_spec_contains_key'address_u64'(t: (Table int (int)), k: int): bool {
    ContainsTable(t, $EncodeKey'address'(k))
}
function {:inline} $1_simple_map_spec_set'address_u64'(t: Table int (int), k: int, v: int): Table int (int) {
    (var enc_k := $EncodeKey'address'(k);
    if (ContainsTable(t, enc_k)) then
        UpdateTable(t, enc_k, v)
    else
        AddTable(t, enc_k, v))
}
function {:inline} $1_simple_map_spec_remove'address_u64'(t: Table int (int), k: int): Table int (int) {
    RemoveTable(t, $EncodeKey'address'(k))
}
function {:inline} $1_simple_map_spec_get'address_u64'(t: Table int (int), k: int): int {
    GetTable(t, $EncodeKey'address'(k))
}



// ----------------------------------------------------------------------------------
// Native Table implementation for type `(address,bv64)`

function $IsEqual'$1_simple_map_SimpleMap'address_bv64''(t1: Table int (bv64), t2: Table int (bv64)): bool {
    LenTable(t1) == LenTable(t2) &&
    (forall k: int :: ContainsTable(t1, k) <==> ContainsTable(t2, k)) &&
    (forall k: int :: ContainsTable(t1, k) ==> GetTable(t1, k) == GetTable(t2, k)) &&
    (forall k: int :: ContainsTable(t2, k) ==> GetTable(t1, k) == GetTable(t2, k))
}

// Not inlined.
function $IsValid'$1_simple_map_SimpleMap'address_bv64''(t: Table int (bv64)): bool {
    $IsValid'u64'(LenTable(t)) &&
    (forall i: int:: ContainsTable(t, i) ==> $IsValid'bv64'(GetTable(t, i)))
}
procedure {:inline 2} $1_simple_map_create'address_bv64'() returns (v: Table int (bv64)) {
    v := EmptyTable();
}
procedure {:inline 2} $1_simple_map_destroy_empty'address_bv64'(t: Table int (bv64)) {
    if (LenTable(t) != 0) {
        call $Abort($StdError(1/*INVALID_STATE*/, 102/*ENOT_EMPTY*/));
    }
}
procedure {:inline 2} $1_simple_map_length'address_bv64'(t: (Table int (bv64))) returns (l: int) {
    l := LenTable(t);
}
procedure {:inline 2} $1_simple_map_contains_key'address_bv64'(t: (Table int (bv64)), k: int) returns (r: bool) {
    r := ContainsTable(t, $EncodeKey'address'(k));
}
procedure {:inline 2} $1_simple_map_add'address_bv64'(m: $Mutation (Table int (bv64)), k: int, v: bv64) returns (m': $Mutation(Table int (bv64))) {
    var enc_k: int;
    var t: Table int (bv64);
    enc_k := $EncodeKey'address'(k);
    t := $Dereference(m);
    if (ContainsTable(t, enc_k)) {
        call $Abort($StdError(7/*INVALID_ARGUMENTS*/, 100/*EALREADY_EXISTS*/));
    } else {
        m' := $UpdateMutation(m, AddTable(t, enc_k, v));
    }
}
procedure {:inline 2} $1_simple_map_remove'address_bv64'(m: $Mutation (Table int (bv64)), k: int)
returns (k': int, v: bv64, m': $Mutation(Table int (bv64))) {
    var enc_k: int;
    var t: Table int (bv64);
    enc_k := $EncodeKey'address'(k);
    t := $Dereference(m);
    if (!ContainsTable(t, enc_k)) {
        call $Abort($StdError(7/*INVALID_ARGUMENTS*/, 101/*ENOT_FOUND*/));
    } else {
        k' := k;
        v := GetTable(t, enc_k);
        m' := $UpdateMutation(m, RemoveTable(t, enc_k));
    }
}
procedure {:inline 2} $1_simple_map_borrow'address_bv64'(t: Table int (bv64), k: int) returns (v: bv64) {
    var enc_k: int;
    enc_k := $EncodeKey'address'(k);
    if (!ContainsTable(t, enc_k)) {
        call $Abort($StdError(7/*INVALID_ARGUMENTS*/, 101/*ENOT_FOUND*/));
    } else {
        v := GetTable(t, $EncodeKey'address'(k));
    }
}
procedure {:inline 2} $1_simple_map_borrow_mut'address_bv64'(m: $Mutation (Table int (bv64)), k: int)
returns (dst: $Mutation (bv64), m': $Mutation (Table int (bv64))) {
    var enc_k: int;
    var t: Table int (bv64);
    enc_k := $EncodeKey'address'(k);
    t := $Dereference(m);
    if (!ContainsTable(t, enc_k)) {
        call $Abort($StdError(7/*INVALID_ARGUMENTS*/, 101/*ENOT_FOUND*/));
    } else {
        dst := $Mutation(l#$Mutation(m), ExtendVec(p#$Mutation(m), enc_k), GetTable(t, enc_k));
        m' := m;
    }
}
function {:inline} $1_simple_map_spec_len'address_bv64'(t: (Table int (bv64))): int {
    LenTable(t)
}
function {:inline} $1_simple_map_spec_contains_key'address_bv64'(t: (Table int (bv64)), k: int): bool {
    ContainsTable(t, $EncodeKey'address'(k))
}
function {:inline} $1_simple_map_spec_set'address_bv64'(t: Table int (bv64), k: int, v: bv64): Table int (bv64) {
    (var enc_k := $EncodeKey'address'(k);
    if (ContainsTable(t, enc_k)) then
        UpdateTable(t, enc_k, v)
    else
        AddTable(t, enc_k, v))
}
function {:inline} $1_simple_map_spec_remove'address_bv64'(t: Table int (bv64), k: int): Table int (bv64) {
    RemoveTable(t, $EncodeKey'address'(k))
}
function {:inline} $1_simple_map_spec_get'address_bv64'(t: Table int (bv64), k: int): bv64 {
    GetTable(t, $EncodeKey'address'(k))
}



// ==================================================================================
// Native Hash

// Hash is modeled as an otherwise uninterpreted injection.
// In truth, it is not an injection since the domain has greater cardinality
// (arbitrary length vectors) than the co-domain (vectors of length 32).  But it is
// common to assume in code there are no hash collisions in practice.  Fortunately,
// Boogie is not smart enough to recognized that there is an inconsistency.
// FIXME: If we were using a reliable extensional theory of arrays, and if we could use ==
// instead of $IsEqual, we might be able to avoid so many quantified formulas by
// using a sha2_inverse function in the ensures conditions of Hash_sha2_256 to
// assert that sha2/3 are injections without using global quantified axioms.


function $1_hash_sha2(val: Vec int): Vec int;

// This says that Hash_sha2 is bijective.
axiom (forall v1,v2: Vec int :: {$1_hash_sha2(v1), $1_hash_sha2(v2)}
       $IsEqual'vec'u8''(v1, v2) <==> $IsEqual'vec'u8''($1_hash_sha2(v1), $1_hash_sha2(v2)));

procedure $1_hash_sha2_256(val: Vec int) returns (res: Vec int);
ensures res == $1_hash_sha2(val);     // returns Hash_sha2 Value
ensures $IsValid'vec'u8''(res);    // result is a legal vector of U8s.
ensures LenVec(res) == 32;               // result is 32 bytes.

// Spec version of Move native function.
function {:inline} $1_hash_$sha2_256(val: Vec int): Vec int {
    $1_hash_sha2(val)
}

// similarly for Hash_sha3
function $1_hash_sha3(val: Vec int): Vec int;

axiom (forall v1,v2: Vec int :: {$1_hash_sha3(v1), $1_hash_sha3(v2)}
       $IsEqual'vec'u8''(v1, v2) <==> $IsEqual'vec'u8''($1_hash_sha3(v1), $1_hash_sha3(v2)));

procedure $1_hash_sha3_256(val: Vec int) returns (res: Vec int);
ensures res == $1_hash_sha3(val);     // returns Hash_sha3 Value
ensures $IsValid'vec'u8''(res);    // result is a legal vector of U8s.
ensures LenVec(res) == 32;               // result is 32 bytes.

// Spec version of Move native function.
function {:inline} $1_hash_$sha3_256(val: Vec int): Vec int {
    $1_hash_sha3(val)
}

// ==================================================================================
// Native string

// TODO: correct implementation of strings

procedure {:inline 1} $1_string_internal_check_utf8(x: Vec int) returns (r: bool) {
}

procedure {:inline 1} $1_string_internal_sub_string(x: Vec int, i: int, j: int) returns (r: Vec int) {
}

procedure {:inline 1} $1_string_internal_index_of(x: Vec int, y: Vec int) returns (r: int) {
}

procedure {:inline 1} $1_string_internal_is_char_boundary(x: Vec int, i: int) returns (r: bool) {
}




// ==================================================================================
// Native diem_account

procedure {:inline 1} $1_DiemAccount_create_signer(
  addr: int
) returns (signer: $signer) {
    // A signer is currently identical to an address.
    signer := $signer(addr);
}

procedure {:inline 1} $1_DiemAccount_destroy_signer(
  signer: $signer
) {
  return;
}

// ==================================================================================
// Native account

procedure {:inline 1} $1_Account_create_signer(
  addr: int
) returns (signer: $signer) {
    // A signer is currently identical to an address.
    signer := $signer(addr);
}

// ==================================================================================
// Native Signer

type {:datatype} $signer;
function {:constructor} $signer($addr: int): $signer;
function {:inline} $IsValid'signer'(s: $signer): bool {
    $IsValid'address'($addr#$signer(s))
}
function {:inline} $IsEqual'signer'(s1: $signer, s2: $signer): bool {
    s1 == s2
}

procedure {:inline 1} $1_signer_borrow_address(signer: $signer) returns (res: int) {
    res := $addr#$signer(signer);
}

function {:inline} $1_signer_$borrow_address(signer: $signer): int
{
    $addr#$signer(signer)
}

function $1_signer_is_txn_signer(s: $signer): bool;

function $1_signer_is_txn_signer_addr(a: int): bool;


// ==================================================================================
// Native signature

// Signature related functionality is handled via uninterpreted functions. This is sound
// currently because we verify every code path based on signature verification with
// an arbitrary interpretation.

function $1_Signature_$ed25519_validate_pubkey(public_key: Vec int): bool;
function $1_Signature_$ed25519_verify(signature: Vec int, public_key: Vec int, message: Vec int): bool;

// Needed because we do not have extensional equality:
axiom (forall k1, k2: Vec int ::
    {$1_Signature_$ed25519_validate_pubkey(k1), $1_Signature_$ed25519_validate_pubkey(k2)}
    $IsEqual'vec'u8''(k1, k2) ==> $1_Signature_$ed25519_validate_pubkey(k1) == $1_Signature_$ed25519_validate_pubkey(k2));
axiom (forall s1, s2, k1, k2, m1, m2: Vec int ::
    {$1_Signature_$ed25519_verify(s1, k1, m1), $1_Signature_$ed25519_verify(s2, k2, m2)}
    $IsEqual'vec'u8''(s1, s2) && $IsEqual'vec'u8''(k1, k2) && $IsEqual'vec'u8''(m1, m2)
    ==> $1_Signature_$ed25519_verify(s1, k1, m1) == $1_Signature_$ed25519_verify(s2, k2, m2));


procedure {:inline 1} $1_Signature_ed25519_validate_pubkey(public_key: Vec int) returns (res: bool) {
    res := $1_Signature_$ed25519_validate_pubkey(public_key);
}

procedure {:inline 1} $1_Signature_ed25519_verify(
        signature: Vec int, public_key: Vec int, message: Vec int) returns (res: bool) {
    res := $1_Signature_$ed25519_verify(signature, public_key, message);
}


// ==================================================================================
// Native bcs::serialize


// ==================================================================================
// Native Event module



procedure {:inline 1} $InitEventStore() {
}

// ============================================================================================
// Type Reflection on Type Parameters

type {:datatype} $TypeParamInfo;

function {:constructor} $TypeParamBool(): $TypeParamInfo;
function {:constructor} $TypeParamU8(): $TypeParamInfo;
function {:constructor} $TypeParamU16(): $TypeParamInfo;
function {:constructor} $TypeParamU32(): $TypeParamInfo;
function {:constructor} $TypeParamU64(): $TypeParamInfo;
function {:constructor} $TypeParamU128(): $TypeParamInfo;
function {:constructor} $TypeParamU256(): $TypeParamInfo;
function {:constructor} $TypeParamAddress(): $TypeParamInfo;
function {:constructor} $TypeParamSigner(): $TypeParamInfo;
function {:constructor} $TypeParamVector(e: $TypeParamInfo): $TypeParamInfo;
function {:constructor} $TypeParamStruct(a: int, m: Vec int, s: Vec int): $TypeParamInfo;



//==================================
// Begin Translation

function $TypeName(t: $TypeParamInfo): Vec int;
axiom (forall t: $TypeParamInfo :: {$TypeName(t)} is#$TypeParamBool(t) ==> $IsEqual'vec'u8''($TypeName(t), Vec(DefaultVecMap()[0 := 98][1 := 111][2 := 111][3 := 108], 4)));
axiom (forall t: $TypeParamInfo :: {$TypeName(t)} $IsEqual'vec'u8''($TypeName(t), Vec(DefaultVecMap()[0 := 98][1 := 111][2 := 111][3 := 108], 4)) ==> is#$TypeParamBool(t));
axiom (forall t: $TypeParamInfo :: {$TypeName(t)} is#$TypeParamU8(t) ==> $IsEqual'vec'u8''($TypeName(t), Vec(DefaultVecMap()[0 := 117][1 := 56], 2)));
axiom (forall t: $TypeParamInfo :: {$TypeName(t)} $IsEqual'vec'u8''($TypeName(t), Vec(DefaultVecMap()[0 := 117][1 := 56], 2)) ==> is#$TypeParamU8(t));
axiom (forall t: $TypeParamInfo :: {$TypeName(t)} is#$TypeParamU16(t) ==> $IsEqual'vec'u8''($TypeName(t), Vec(DefaultVecMap()[0 := 117][1 := 49][2 := 54], 3)));
axiom (forall t: $TypeParamInfo :: {$TypeName(t)} $IsEqual'vec'u8''($TypeName(t), Vec(DefaultVecMap()[0 := 117][1 := 49][2 := 54], 3)) ==> is#$TypeParamU16(t));
axiom (forall t: $TypeParamInfo :: {$TypeName(t)} is#$TypeParamU32(t) ==> $IsEqual'vec'u8''($TypeName(t), Vec(DefaultVecMap()[0 := 117][1 := 51][2 := 50], 3)));
axiom (forall t: $TypeParamInfo :: {$TypeName(t)} $IsEqual'vec'u8''($TypeName(t), Vec(DefaultVecMap()[0 := 117][1 := 51][2 := 50], 3)) ==> is#$TypeParamU32(t));
axiom (forall t: $TypeParamInfo :: {$TypeName(t)} is#$TypeParamU64(t) ==> $IsEqual'vec'u8''($TypeName(t), Vec(DefaultVecMap()[0 := 117][1 := 54][2 := 52], 3)));
axiom (forall t: $TypeParamInfo :: {$TypeName(t)} $IsEqual'vec'u8''($TypeName(t), Vec(DefaultVecMap()[0 := 117][1 := 54][2 := 52], 3)) ==> is#$TypeParamU64(t));
axiom (forall t: $TypeParamInfo :: {$TypeName(t)} is#$TypeParamU128(t) ==> $IsEqual'vec'u8''($TypeName(t), Vec(DefaultVecMap()[0 := 117][1 := 49][2 := 50][3 := 56], 4)));
axiom (forall t: $TypeParamInfo :: {$TypeName(t)} $IsEqual'vec'u8''($TypeName(t), Vec(DefaultVecMap()[0 := 117][1 := 49][2 := 50][3 := 56], 4)) ==> is#$TypeParamU128(t));
axiom (forall t: $TypeParamInfo :: {$TypeName(t)} is#$TypeParamU256(t) ==> $IsEqual'vec'u8''($TypeName(t), Vec(DefaultVecMap()[0 := 117][1 := 50][2 := 53][3 := 54], 4)));
axiom (forall t: $TypeParamInfo :: {$TypeName(t)} $IsEqual'vec'u8''($TypeName(t), Vec(DefaultVecMap()[0 := 117][1 := 50][2 := 53][3 := 54], 4)) ==> is#$TypeParamU256(t));
axiom (forall t: $TypeParamInfo :: {$TypeName(t)} is#$TypeParamAddress(t) ==> $IsEqual'vec'u8''($TypeName(t), Vec(DefaultVecMap()[0 := 97][1 := 100][2 := 100][3 := 114][4 := 101][5 := 115][6 := 115], 7)));
axiom (forall t: $TypeParamInfo :: {$TypeName(t)} $IsEqual'vec'u8''($TypeName(t), Vec(DefaultVecMap()[0 := 97][1 := 100][2 := 100][3 := 114][4 := 101][5 := 115][6 := 115], 7)) ==> is#$TypeParamAddress(t));
axiom (forall t: $TypeParamInfo :: {$TypeName(t)} is#$TypeParamSigner(t) ==> $IsEqual'vec'u8''($TypeName(t), Vec(DefaultVecMap()[0 := 115][1 := 105][2 := 103][3 := 110][4 := 101][5 := 114], 6)));
axiom (forall t: $TypeParamInfo :: {$TypeName(t)} $IsEqual'vec'u8''($TypeName(t), Vec(DefaultVecMap()[0 := 115][1 := 105][2 := 103][3 := 110][4 := 101][5 := 114], 6)) ==> is#$TypeParamSigner(t));
axiom (forall t: $TypeParamInfo :: {$TypeName(t)} is#$TypeParamVector(t) ==> $IsEqual'vec'u8''($TypeName(t), ConcatVec(ConcatVec(Vec(DefaultVecMap()[0 := 118][1 := 101][2 := 99][3 := 116][4 := 111][5 := 114][6 := 60], 7), $TypeName(e#$TypeParamVector(t))), Vec(DefaultVecMap()[0 := 62], 1))));
axiom (forall t: $TypeParamInfo :: {$TypeName(t)} ($IsPrefix'vec'u8''($TypeName(t), Vec(DefaultVecMap()[0 := 118][1 := 101][2 := 99][3 := 116][4 := 111][5 := 114][6 := 60], 7)) && $IsSuffix'vec'u8''($TypeName(t), Vec(DefaultVecMap()[0 := 62], 1))) ==> is#$TypeParamVector(t));
axiom (forall t: $TypeParamInfo :: {$TypeName(t)} is#$TypeParamStruct(t) ==> $IsEqual'vec'u8''($TypeName(t), ConcatVec(ConcatVec(ConcatVec(ConcatVec(ConcatVec(Vec(DefaultVecMap()[0 := 48][1 := 120], 2), MakeVec1(a#$TypeParamStruct(t))), Vec(DefaultVecMap()[0 := 58][1 := 58], 2)), m#$TypeParamStruct(t)), Vec(DefaultVecMap()[0 := 58][1 := 58], 2)), s#$TypeParamStruct(t))));
axiom (forall t: $TypeParamInfo :: {$TypeName(t)} $IsPrefix'vec'u8''($TypeName(t), Vec(DefaultVecMap()[0 := 48][1 := 120], 2)) ==> is#$TypeParamVector(t));


// Given Types for Type Parameters

type #0;
function {:inline} $IsEqual'#0'(x1: #0, x2: #0): bool { x1 == x2 }
function {:inline} $IsValid'#0'(x: #0): bool { true }
var #0_info: $TypeParamInfo;
var #0_$memory: $Memory #0;

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:14:9+116, instance <bool>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'bool'($1_from_bcs_deserialize'bool'(b1), $1_from_bcs_deserialize'bool'(b2)) ==> $IsEqual'vec'u8''(b1, b2))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:14:9+116, instance <u64>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'u64'($1_from_bcs_deserialize'u64'(b1), $1_from_bcs_deserialize'u64'(b2)) ==> $IsEqual'vec'u8''(b1, b2))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:14:9+116, instance <u128>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'u128'($1_from_bcs_deserialize'u128'(b1), $1_from_bcs_deserialize'u128'(b2)) ==> $IsEqual'vec'u8''(b1, b2))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:14:9+116, instance <u256>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'u256'($1_from_bcs_deserialize'u256'(b1), $1_from_bcs_deserialize'u256'(b2)) ==> $IsEqual'vec'u8''(b1, b2))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:14:9+116, instance <address>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'address'($1_from_bcs_deserialize'address'(b1), $1_from_bcs_deserialize'address'(b2)) ==> $IsEqual'vec'u8''(b1, b2))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:14:9+116, instance <vector<u8>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''($1_from_bcs_deserialize'vec'u8''(b1), $1_from_bcs_deserialize'vec'u8''(b2)) ==> $IsEqual'vec'u8''(b1, b2))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:14:9+116, instance <vector<address>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'address''($1_from_bcs_deserialize'vec'address''(b1), $1_from_bcs_deserialize'vec'address''(b2)) ==> $IsEqual'vec'u8''(b1, b2))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:14:9+116, instance <simple_map::SimpleMap<address, u64>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'$1_simple_map_SimpleMap'address_u64''($1_from_bcs_deserialize'$1_simple_map_SimpleMap'address_u64''(b1), $1_from_bcs_deserialize'$1_simple_map_SimpleMap'address_u64''(b2)) ==> $IsEqual'vec'u8''(b1, b2))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:14:9+116, instance <pool_u64::Pool>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'$1_pool_u64_Pool'($1_from_bcs_deserialize'$1_pool_u64_Pool'(b1), $1_from_bcs_deserialize'$1_pool_u64_Pool'(b2)) ==> $IsEqual'vec'u8''(b1, b2))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:14:9+116, instance <#0>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'#0'($1_from_bcs_deserialize'#0'(b1), $1_from_bcs_deserialize'#0'(b2)) ==> $IsEqual'vec'u8''(b1, b2))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:18:9+124, instance <bool>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'bool'($1_from_bcs_deserializable'bool'(b1), $1_from_bcs_deserializable'bool'(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:18:9+124, instance <u64>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'bool'($1_from_bcs_deserializable'u64'(b1), $1_from_bcs_deserializable'u64'(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:18:9+124, instance <u128>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'bool'($1_from_bcs_deserializable'u128'(b1), $1_from_bcs_deserializable'u128'(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:18:9+124, instance <u256>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'bool'($1_from_bcs_deserializable'u256'(b1), $1_from_bcs_deserializable'u256'(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:18:9+124, instance <address>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'bool'($1_from_bcs_deserializable'address'(b1), $1_from_bcs_deserializable'address'(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:18:9+124, instance <vector<u8>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'bool'($1_from_bcs_deserializable'vec'u8''(b1), $1_from_bcs_deserializable'vec'u8''(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:18:9+124, instance <vector<address>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'bool'($1_from_bcs_deserializable'vec'address''(b1), $1_from_bcs_deserializable'vec'address''(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:18:9+124, instance <simple_map::SimpleMap<address, u64>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'bool'($1_from_bcs_deserializable'$1_simple_map_SimpleMap'address_u64''(b1), $1_from_bcs_deserializable'$1_simple_map_SimpleMap'address_u64''(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:18:9+124, instance <pool_u64::Pool>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'bool'($1_from_bcs_deserializable'$1_pool_u64_Pool'(b1), $1_from_bcs_deserializable'$1_pool_u64_Pool'(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:18:9+124, instance <#0>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'bool'($1_from_bcs_deserializable'#0'(b1), $1_from_bcs_deserializable'#0'(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:21:9+118, instance <bool>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'bool'($1_from_bcs_deserialize'bool'(b1), $1_from_bcs_deserialize'bool'(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:21:9+118, instance <u64>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'u64'($1_from_bcs_deserialize'u64'(b1), $1_from_bcs_deserialize'u64'(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:21:9+118, instance <u128>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'u128'($1_from_bcs_deserialize'u128'(b1), $1_from_bcs_deserialize'u128'(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:21:9+118, instance <u256>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'u256'($1_from_bcs_deserialize'u256'(b1), $1_from_bcs_deserialize'u256'(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:21:9+118, instance <address>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'address'($1_from_bcs_deserialize'address'(b1), $1_from_bcs_deserialize'address'(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:21:9+118, instance <vector<u8>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'vec'u8''($1_from_bcs_deserialize'vec'u8''(b1), $1_from_bcs_deserialize'vec'u8''(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:21:9+118, instance <vector<address>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'vec'address''($1_from_bcs_deserialize'vec'address''(b1), $1_from_bcs_deserialize'vec'address''(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:21:9+118, instance <simple_map::SimpleMap<address, u64>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'$1_simple_map_SimpleMap'address_u64''($1_from_bcs_deserialize'$1_simple_map_SimpleMap'address_u64''(b1), $1_from_bcs_deserialize'$1_simple_map_SimpleMap'address_u64''(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:21:9+118, instance <pool_u64::Pool>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'$1_pool_u64_Pool'($1_from_bcs_deserialize'$1_pool_u64_Pool'(b1), $1_from_bcs_deserialize'$1_pool_u64_Pool'(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:21:9+118, instance <#0>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'#0'($1_from_bcs_deserialize'#0'(b1), $1_from_bcs_deserialize'#0'(b2)))));

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/../move-stdlib/sources/vector.move:471:9+110
function {:inline} $1_vector_spec_contains'address'(v: Vec (int), e: int): bool {
    (var $range_0 := v; (exists $i_1: int :: InRangeVec($range_0, $i_1) && (var x := ReadVec($range_0, $i_1);
    ($IsEqual'address'(x, e)))))
}

// fun error::invalid_argument [baseline] at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/../move-stdlib/sources/error.move:76:3+76
procedure {:inline 1} $1_error_invalid_argument(_$t0: int) returns ($ret0: int)
{
    // declare local variables
    var $t1: int;
    var $t2: int;
    var $t3: int;
    var $t0: int;
    var $temp_0'u64': int;
    $t0 := _$t0;

    // bytecode translation starts here
    // trace_local[r]($t0) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/../move-stdlib/sources/error.move:76:3+1
    assume {:print "$at(10,3082,3083)"} true;
    assume {:print "$track_local(4,4,0):", $t0} $t0 == $t0;

    // $t1 := 1 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/../move-stdlib/sources/error.move:76:57+16
    $t1 := 1;
    assume $IsValid'u64'($t1);

    // assume Identical($t2, Shl($t1, 16)) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/../move-stdlib/sources/error.move:69:5+29
    assume {:print "$at(10,2844,2873)"} true;
    assume ($t2 == $shlU64($t1, 16));

    // $t3 := opaque begin: error::canonical($t1, $t0) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/../move-stdlib/sources/error.move:76:47+30
    assume {:print "$at(10,3126,3156)"} true;

    // assume WellFormed($t3) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/../move-stdlib/sources/error.move:76:47+30
    assume $IsValid'u64'($t3);

    // assume Eq<u64>($t3, $t1) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/../move-stdlib/sources/error.move:76:47+30
    assume $IsEqual'u64'($t3, $t1);

    // $t3 := opaque end: error::canonical($t1, $t0) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/../move-stdlib/sources/error.move:76:47+30

    // trace_return[0]($t3) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/../move-stdlib/sources/error.move:76:47+30
    assume {:print "$track_return(4,4,0):", $t3} $t3 == $t3;

    // label L1 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/../move-stdlib/sources/error.move:76:78+1
L1:

    // return $t3 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/../move-stdlib/sources/error.move:76:78+1
    assume {:print "$at(10,3157,3158)"} true;
    $ret0 := $t3;
    return;

}

// fun error::invalid_state [baseline] at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/../move-stdlib/sources/error.move:78:3+70
procedure {:inline 1} $1_error_invalid_state(_$t0: int) returns ($ret0: int)
{
    // declare local variables
    var $t1: int;
    var $t2: int;
    var $t3: int;
    var $t0: int;
    var $temp_0'u64': int;
    $t0 := _$t0;

    // bytecode translation starts here
    // trace_local[r]($t0) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/../move-stdlib/sources/error.move:78:3+1
    assume {:print "$at(10,3232,3233)"} true;
    assume {:print "$track_local(4,5,0):", $t0} $t0 == $t0;

    // $t1 := 3 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/../move-stdlib/sources/error.move:78:54+13
    $t1 := 3;
    assume $IsValid'u64'($t1);

    // assume Identical($t2, Shl($t1, 16)) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/../move-stdlib/sources/error.move:69:5+29
    assume {:print "$at(10,2844,2873)"} true;
    assume ($t2 == $shlU64($t1, 16));

    // $t3 := opaque begin: error::canonical($t1, $t0) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/../move-stdlib/sources/error.move:78:44+27
    assume {:print "$at(10,3273,3300)"} true;

    // assume WellFormed($t3) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/../move-stdlib/sources/error.move:78:44+27
    assume $IsValid'u64'($t3);

    // assume Eq<u64>($t3, $t1) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/../move-stdlib/sources/error.move:78:44+27
    assume $IsEqual'u64'($t3, $t1);

    // $t3 := opaque end: error::canonical($t1, $t0) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/../move-stdlib/sources/error.move:78:44+27

    // trace_return[0]($t3) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/../move-stdlib/sources/error.move:78:44+27
    assume {:print "$track_return(4,5,0):", $t3} $t3 == $t3;

    // label L1 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/../move-stdlib/sources/error.move:78:72+1
L1:

    // return $t3 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/../move-stdlib/sources/error.move:78:72+1
    assume {:print "$at(10,3301,3302)"} true;
    $ret0 := $t3;
    return;

}

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:7:9+41
function  $1_from_bcs_deserialize'bool'(bytes: Vec (int)): bool;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserialize'bool'(bytes);
$IsValid'bool'($$res)));

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:7:9+41
function  $1_from_bcs_deserialize'u64'(bytes: Vec (int)): int;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserialize'u64'(bytes);
$IsValid'u64'($$res)));

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:7:9+41
function  $1_from_bcs_deserialize'u128'(bytes: Vec (int)): int;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserialize'u128'(bytes);
$IsValid'u128'($$res)));

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:7:9+41
function  $1_from_bcs_deserialize'u256'(bytes: Vec (int)): int;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserialize'u256'(bytes);
$IsValid'u256'($$res)));

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:7:9+41
function  $1_from_bcs_deserialize'address'(bytes: Vec (int)): int;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserialize'address'(bytes);
$IsValid'address'($$res)));

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:7:9+41
function  $1_from_bcs_deserialize'vec'u8''(bytes: Vec (int)): Vec (int);
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserialize'vec'u8''(bytes);
$IsValid'vec'u8''($$res)));

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:7:9+41
function  $1_from_bcs_deserialize'vec'address''(bytes: Vec (int)): Vec (int);
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserialize'vec'address''(bytes);
$IsValid'vec'address''($$res)));

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:7:9+41
function  $1_from_bcs_deserialize'$1_simple_map_SimpleMap'address_u64''(bytes: Vec (int)): Table int (int);
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserialize'$1_simple_map_SimpleMap'address_u64''(bytes);
$IsValid'$1_simple_map_SimpleMap'address_u64''($$res)));

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:7:9+41
function  $1_from_bcs_deserialize'$1_pool_u64_Pool'(bytes: Vec (int)): $1_pool_u64_Pool;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserialize'$1_pool_u64_Pool'(bytes);
$IsValid'$1_pool_u64_Pool'($$res)));

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:7:9+41
function  $1_from_bcs_deserialize'#0'(bytes: Vec (int)): #0;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserialize'#0'(bytes);
$IsValid'#0'($$res)));

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:11:9+47
function  $1_from_bcs_deserializable'bool'(bytes: Vec (int)): bool;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserializable'bool'(bytes);
$IsValid'bool'($$res)));

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:11:9+47
function  $1_from_bcs_deserializable'u64'(bytes: Vec (int)): bool;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserializable'u64'(bytes);
$IsValid'bool'($$res)));

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:11:9+47
function  $1_from_bcs_deserializable'u128'(bytes: Vec (int)): bool;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserializable'u128'(bytes);
$IsValid'bool'($$res)));

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:11:9+47
function  $1_from_bcs_deserializable'u256'(bytes: Vec (int)): bool;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserializable'u256'(bytes);
$IsValid'bool'($$res)));

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:11:9+47
function  $1_from_bcs_deserializable'address'(bytes: Vec (int)): bool;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserializable'address'(bytes);
$IsValid'bool'($$res)));

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:11:9+47
function  $1_from_bcs_deserializable'vec'u8''(bytes: Vec (int)): bool;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserializable'vec'u8''(bytes);
$IsValid'bool'($$res)));

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:11:9+47
function  $1_from_bcs_deserializable'vec'address''(bytes: Vec (int)): bool;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserializable'vec'address''(bytes);
$IsValid'bool'($$res)));

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:11:9+47
function  $1_from_bcs_deserializable'$1_simple_map_SimpleMap'address_u64''(bytes: Vec (int)): bool;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserializable'$1_simple_map_SimpleMap'address_u64''(bytes);
$IsValid'bool'($$res)));

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:11:9+47
function  $1_from_bcs_deserializable'$1_pool_u64_Pool'(bytes: Vec (int)): bool;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserializable'$1_pool_u64_Pool'(bytes);
$IsValid'bool'($$res)));

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:11:9+47
function  $1_from_bcs_deserializable'#0'(bytes: Vec (int)): bool;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserializable'#0'(bytes);
$IsValid'bool'($$res)));

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.spec.move:29:10+129
function {:inline} $1_pool_u64_spec_contains(pool: $1_pool_u64_Pool, shareholder: int): bool {
    $1_simple_map_spec_contains_key'address_u64'($shares#$1_pool_u64_Pool(pool), shareholder)
}

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.spec.move:38:10+241
function {:inline} $1_pool_u64_spec_shares(pool: $1_pool_u64_Pool, shareholder: int): int {
    (if ($1_simple_map_spec_contains_key'address_u64'($shares#$1_pool_u64_Pool(pool), shareholder)) then ($1_simple_map_spec_get'address_u64'($shares#$1_pool_u64_Pool(pool), shareholder)) else (0))
}

// struct pool_u64::Pool at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:38:5+449
type {:datatype} $1_pool_u64_Pool;
function {:constructor} $1_pool_u64_Pool($shareholders_limit: int, $total_coins: int, $total_shares: int, $shares: Table int (int), $shareholders: Vec (int), $scaling_factor: int): $1_pool_u64_Pool;
function {:inline} $Update'$1_pool_u64_Pool'_shareholders_limit(s: $1_pool_u64_Pool, x: int): $1_pool_u64_Pool {
    $1_pool_u64_Pool(x, $total_coins#$1_pool_u64_Pool(s), $total_shares#$1_pool_u64_Pool(s), $shares#$1_pool_u64_Pool(s), $shareholders#$1_pool_u64_Pool(s), $scaling_factor#$1_pool_u64_Pool(s))
}
function {:inline} $Update'$1_pool_u64_Pool'_total_coins(s: $1_pool_u64_Pool, x: int): $1_pool_u64_Pool {
    $1_pool_u64_Pool($shareholders_limit#$1_pool_u64_Pool(s), x, $total_shares#$1_pool_u64_Pool(s), $shares#$1_pool_u64_Pool(s), $shareholders#$1_pool_u64_Pool(s), $scaling_factor#$1_pool_u64_Pool(s))
}
function {:inline} $Update'$1_pool_u64_Pool'_total_shares(s: $1_pool_u64_Pool, x: int): $1_pool_u64_Pool {
    $1_pool_u64_Pool($shareholders_limit#$1_pool_u64_Pool(s), $total_coins#$1_pool_u64_Pool(s), x, $shares#$1_pool_u64_Pool(s), $shareholders#$1_pool_u64_Pool(s), $scaling_factor#$1_pool_u64_Pool(s))
}
function {:inline} $Update'$1_pool_u64_Pool'_shares(s: $1_pool_u64_Pool, x: Table int (int)): $1_pool_u64_Pool {
    $1_pool_u64_Pool($shareholders_limit#$1_pool_u64_Pool(s), $total_coins#$1_pool_u64_Pool(s), $total_shares#$1_pool_u64_Pool(s), x, $shareholders#$1_pool_u64_Pool(s), $scaling_factor#$1_pool_u64_Pool(s))
}
function {:inline} $Update'$1_pool_u64_Pool'_shareholders(s: $1_pool_u64_Pool, x: Vec (int)): $1_pool_u64_Pool {
    $1_pool_u64_Pool($shareholders_limit#$1_pool_u64_Pool(s), $total_coins#$1_pool_u64_Pool(s), $total_shares#$1_pool_u64_Pool(s), $shares#$1_pool_u64_Pool(s), x, $scaling_factor#$1_pool_u64_Pool(s))
}
function {:inline} $Update'$1_pool_u64_Pool'_scaling_factor(s: $1_pool_u64_Pool, x: int): $1_pool_u64_Pool {
    $1_pool_u64_Pool($shareholders_limit#$1_pool_u64_Pool(s), $total_coins#$1_pool_u64_Pool(s), $total_shares#$1_pool_u64_Pool(s), $shares#$1_pool_u64_Pool(s), $shareholders#$1_pool_u64_Pool(s), x)
}
function $IsValid'$1_pool_u64_Pool'(s: $1_pool_u64_Pool): bool {
    $IsValid'u64'($shareholders_limit#$1_pool_u64_Pool(s))
      && $IsValid'u64'($total_coins#$1_pool_u64_Pool(s))
      && $IsValid'u64'($total_shares#$1_pool_u64_Pool(s))
      && $IsValid'$1_simple_map_SimpleMap'address_u64''($shares#$1_pool_u64_Pool(s))
      && $IsValid'vec'address''($shareholders#$1_pool_u64_Pool(s))
      && $IsValid'u64'($scaling_factor#$1_pool_u64_Pool(s))
}
function {:inline} $IsEqual'$1_pool_u64_Pool'(s1: $1_pool_u64_Pool, s2: $1_pool_u64_Pool): bool {
    $IsEqual'u64'($shareholders_limit#$1_pool_u64_Pool(s1), $shareholders_limit#$1_pool_u64_Pool(s2))
    && $IsEqual'u64'($total_coins#$1_pool_u64_Pool(s1), $total_coins#$1_pool_u64_Pool(s2))
    && $IsEqual'u64'($total_shares#$1_pool_u64_Pool(s1), $total_shares#$1_pool_u64_Pool(s2))
    && $IsEqual'$1_simple_map_SimpleMap'address_u64''($shares#$1_pool_u64_Pool(s1), $shares#$1_pool_u64_Pool(s2))
    && $IsEqual'vec'address''($shareholders#$1_pool_u64_Pool(s1), $shareholders#$1_pool_u64_Pool(s2))
    && $IsEqual'u64'($scaling_factor#$1_pool_u64_Pool(s1), $scaling_factor#$1_pool_u64_Pool(s2))}

// fun pool_u64::contains [baseline] at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:91:5+129
procedure {:inline 1} $1_pool_u64_contains(_$t0: $1_pool_u64_Pool, _$t1: int) returns ($ret0: bool)
{
    // declare local variables
    var $t2: Table int (int);
    var $t3: bool;
    var $t4: int;
    var $t0: $1_pool_u64_Pool;
    var $t1: int;
    var $temp_0'$1_pool_u64_Pool': $1_pool_u64_Pool;
    var $temp_0'address': int;
    var $temp_0'bool': bool;
    $t0 := _$t0;
    $t1 := _$t1;

    // bytecode translation starts here
    // trace_local[pool]($t0) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:91:5+1
    assume {:print "$at(58,3640,3641)"} true;
    assume {:print "$track_local(55,5,0):", $t0} $t0 == $t0;

    // trace_local[shareholder]($t1) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:91:5+1
    assume {:print "$track_local(55,5,1):", $t1} $t1 == $t1;

    // $t2 := get_field<pool_u64::Pool>.shares($t0) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:92:34+12
    assume {:print "$at(58,3736,3748)"} true;
    $t2 := $shares#$1_pool_u64_Pool($t0);

    // $t3 := simple_map::contains_key<address, u64>($t2, $t1) on_abort goto L2 with $t4 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:92:9+52
    call $t3 := $1_simple_map_contains_key'address_u64'($t2, $t1);
    if ($abort_flag) {
        assume {:print "$at(58,3711,3763)"} true;
        $t4 := $abort_code;
        assume {:print "$track_abort(55,5):", $t4} $t4 == $t4;
        goto L2;
    }

    // trace_return[0]($t3) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:92:9+52
    assume {:print "$track_return(55,5,0):", $t3} $t3 == $t3;

    // label L1 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:93:5+1
    assume {:print "$at(58,3768,3769)"} true;
L1:

    // return $t3 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:93:5+1
    assume {:print "$at(58,3768,3769)"} true;
    $ret0 := $t3;
    return;

    // label L2 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:93:5+1
L2:

    // abort($t4) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:93:5+1
    assume {:print "$at(58,3768,3769)"} true;
    $abort_code := $t4;
    $abort_flag := true;
    return;

}

// fun pool_u64::to_u128 [baseline] at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:259:5+57
procedure {:inline 1} $1_pool_u64_to_u128(_$t0: int) returns ($ret0: int)
{
    // declare local variables
    var $t1: int;
    var $t2: int;
    var $t0: int;
    var $temp_0'u128': int;
    var $temp_0'u64': int;
    $t0 := _$t0;

    // bytecode translation starts here
    // trace_local[num]($t0) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:259:5+1
    assume {:print "$at(58,11442,11443)"} true;
    assume {:print "$track_local(55,17,0):", $t0} $t0 == $t0;

    // $t1 := (u128)($t0) on_abort goto L2 with $t2 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:260:9+13
    assume {:print "$at(58,11480,11493)"} true;
    call $t1 := $CastU128($t0);
    if ($abort_flag) {
        assume {:print "$at(58,11480,11493)"} true;
        $t2 := $abort_code;
        assume {:print "$track_abort(55,17):", $t2} $t2 == $t2;
        goto L2;
    }

    // trace_return[0]($t1) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:260:9+13
    assume {:print "$track_return(55,17,0):", $t1} $t1 == $t1;

    // label L1 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:261:5+1
    assume {:print "$at(58,11498,11499)"} true;
L1:

    // return $t1 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:261:5+1
    assume {:print "$at(58,11498,11499)"} true;
    $ret0 := $t1;
    return;

    // label L2 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:261:5+1
L2:

    // abort($t2) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:261:5+1
    assume {:print "$at(58,11498,11499)"} true;
    $abort_code := $t2;
    $abort_flag := true;
    return;

}

// fun pool_u64::balance [baseline] at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:105:5+161
procedure {:inline 1} $1_pool_u64_balance(_$t0: $1_pool_u64_Pool, _$t1: int) returns ($ret0: int)
{
    // declare local variables
    var $t2: int;
    var $t3: int;
    var $t4: int;
    var $t5: int;
    var $t6: int;
    var $t7: int;
    var $t0: $1_pool_u64_Pool;
    var $t1: int;
    var $temp_0'$1_pool_u64_Pool': $1_pool_u64_Pool;
    var $temp_0'address': int;
    var $temp_0'u64': int;
    $t0 := _$t0;
    $t1 := _$t1;

    // bytecode translation starts here
    // assume Identical($t3, pool_u64::spec_shares($t0, $t1)) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.spec.move:53:9+44
    assume {:print "$at(59,1730,1774)"} true;
    assume ($t3 == $1_pool_u64_spec_shares($t0, $t1));

    // assume Identical($t4, select pool_u64::Pool.total_coins($t0)) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.spec.move:54:9+35
    assume {:print "$at(59,1783,1818)"} true;
    assume ($t4 == $total_coins#$1_pool_u64_Pool($t0));

    // trace_local[pool]($t0) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:105:5+1
    assume {:print "$at(58,4118,4119)"} true;
    assume {:print "$track_local(55,3,0):", $t0} $t0 == $t0;

    // trace_local[shareholder]($t1) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:105:5+1
    assume {:print "$track_local(55,3,1):", $t1} $t1 == $t1;

    // $t5 := pool_u64::shares($t0, $t1) on_abort goto L2 with $t6 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:106:26+25
    assume {:print "$at(58,4204,4229)"} true;
    call $t5 := $1_pool_u64_shares($t0, $t1);
    if ($abort_flag) {
        assume {:print "$at(58,4204,4229)"} true;
        $t6 := $abort_code;
        assume {:print "$track_abort(55,3):", $t6} $t6 == $t6;
        goto L2;
    }

    // trace_local[num_shares]($t5) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:106:13+10
    assume {:print "$track_local(55,3,2):", $t5} $t5 == $t5;

    // $t7 := pool_u64::shares_to_amount($t0, $t5) on_abort goto L2 with $t6 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:107:9+34
    assume {:print "$at(58,4239,4273)"} true;
    call $t7 := $1_pool_u64_shares_to_amount($t0, $t5);
    if ($abort_flag) {
        assume {:print "$at(58,4239,4273)"} true;
        $t6 := $abort_code;
        assume {:print "$track_abort(55,3):", $t6} $t6 == $t6;
        goto L2;
    }

    // trace_return[0]($t7) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:107:9+34
    assume {:print "$track_return(55,3,0):", $t7} $t7 == $t7;

    // label L1 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:108:5+1
    assume {:print "$at(58,4278,4279)"} true;
L1:

    // return $t7 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:108:5+1
    assume {:print "$at(58,4278,4279)"} true;
    $ret0 := $t7;
    return;

    // label L2 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:108:5+1
L2:

    // abort($t6) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:108:5+1
    assume {:print "$at(58,4278,4279)"} true;
    $abort_code := $t6;
    $abort_flag := true;
    return;

}

// fun pool_u64::add_shares [baseline] at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:141:5+900
procedure {:inline 1} $1_pool_u64_add_shares(_$t0: $Mutation ($1_pool_u64_Pool), _$t1: int, _$t2: int) returns ($ret0: int, $ret1: $Mutation ($1_pool_u64_Pool))
{
    // declare local variables
    var $t3: int;
    var $t4: int;
    var $t5: int;
    var $t6: int;
    var $t7: $Mutation (int);
    var $t8: bool;
    var $t9: bool;
    var $t10: int;
    var $t11: bool;
    var $t12: int;
    var $t13: $1_pool_u64_Pool;
    var $t14: bool;
    var $t15: int;
    var $t16: $Mutation (Table int (int));
    var $t17: $Mutation (int);
    var $t18: int;
    var $t19: int;
    var $t20: int;
    var $t21: bool;
    var $t22: int;
    var $t23: int;
    var $t24: int;
    var $t25: int;
    var $t26: bool;
    var $t27: Vec (int);
    var $t28: int;
    var $t29: int;
    var $t30: bool;
    var $t31: int;
    var $t32: int;
    var $t33: $Mutation (Vec (int));
    var $t34: $Mutation (Table int (int));
    var $t0: $Mutation ($1_pool_u64_Pool);
    var $t1: int;
    var $t2: int;
    var $temp_0'$1_pool_u64_Pool': $1_pool_u64_Pool;
    var $temp_0'address': int;
    var $temp_0'u64': int;
    $t0 := _$t0;
    $t1 := _$t1;
    $t2 := _$t2;

    // bytecode translation starts here
    // assume Identical($t8, simple_map::spec_contains_key<address, u64>(select pool_u64::Pool.shares($t0), $t1)) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.spec.move:74:9+73
    assume {:print "$at(59,2864,2937)"} true;
    assume ($t8 == $1_simple_map_spec_contains_key'address_u64'($shares#$1_pool_u64_Pool($Dereference($t0)), $t1));

    // assume Identical($t9, simple_map::spec_contains_key<address, u64>(select pool_u64::Pool.shares($t0), $t1)) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.spec.move:83:9+73
    assume {:print "$at(59,3186,3259)"} true;
    assume ($t9 == $1_simple_map_spec_contains_key'address_u64'($shares#$1_pool_u64_Pool($Dereference($t0)), $t1));

    // assume Identical($t10, simple_map::spec_get<address, u64>(select pool_u64::Pool.shares($t0), $t1)) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.spec.move:84:9+68
    assume {:print "$at(59,3268,3336)"} true;
    assume ($t10 == $1_simple_map_spec_get'address_u64'($shares#$1_pool_u64_Pool($Dereference($t0)), $t1));

    // assume Identical($t11, simple_map::spec_contains_key<address, u64>(select pool_u64::Pool.shares($t0), $t1)) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.spec.move:94:9+73
    assume {:print "$at(59,3636,3709)"} true;
    assume ($t11 == $1_simple_map_spec_contains_key'address_u64'($shares#$1_pool_u64_Pool($Dereference($t0)), $t1));

    // assume Identical($t12, simple_map::spec_get<address, u64>(select pool_u64::Pool.shares($t0), $t1)) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.spec.move:95:9+68
    assume {:print "$at(59,3718,3786)"} true;
    assume ($t12 == $1_simple_map_spec_get'address_u64'($shares#$1_pool_u64_Pool($Dereference($t0)), $t1));

    // trace_local[pool]($t0) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:141:5+1
    assume {:print "$at(58,5643,5644)"} true;
    $temp_0'$1_pool_u64_Pool' := $Dereference($t0);
    assume {:print "$track_local(55,0,0):", $temp_0'$1_pool_u64_Pool'} $temp_0'$1_pool_u64_Pool' == $temp_0'$1_pool_u64_Pool';

    // trace_local[shareholder]($t1) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:141:5+1
    assume {:print "$track_local(55,0,1):", $t1} $t1 == $t1;

    // trace_local[new_shares]($t2) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:141:5+1
    assume {:print "$track_local(55,0,2):", $t2} $t2 == $t2;

    // $t13 := read_ref($t0) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:142:21+19
    assume {:print "$at(58,5741,5760)"} true;
    $t13 := $Dereference($t0);

    // $t14 := pool_u64::contains($t13, $t1) on_abort goto L14 with $t15 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:142:13+27
    call $t14 := $1_pool_u64_contains($t13, $t1);
    if ($abort_flag) {
        assume {:print "$at(58,5733,5760)"} true;
        $t15 := $abort_code;
        assume {:print "$track_abort(55,0):", $t15} $t15 == $t15;
        goto L14;
    }

    // if ($t14) goto L1 else goto L0 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:142:9+808
    if ($t14) { goto L1; } else { goto L0; }

    // label L1 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:143:63+4
    assume {:print "$at(58,5826,5830)"} true;
L1:

    // $t16 := borrow_field<pool_u64::Pool>.shares($t0) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:143:58+16
    assume {:print "$at(58,5821,5837)"} true;
    $t16 := $ChildMutation($t0, 3, $shares#$1_pool_u64_Pool($Dereference($t0)));

    // $t17 := simple_map::borrow_mut<address, u64>($t16, $t1) on_abort goto L14 with $t15 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:143:35+54
    call $t17,$t16 := $1_simple_map_borrow_mut'address_u64'($t16, $t1);
    if ($abort_flag) {
        assume {:print "$at(58,5798,5852)"} true;
        $t15 := $abort_code;
        assume {:print "$track_abort(55,0):", $t15} $t15 == $t15;
        goto L14;
    }

    // trace_local[existing_shares]($t17) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:143:17+15
    $temp_0'u64' := $Dereference($t17);
    assume {:print "$track_local(55,0,7):", $temp_0'u64'} $temp_0'u64' == $temp_0'u64';

    // $t18 := read_ref($t17) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:144:34+16
    assume {:print "$at(58,5887,5903)"} true;
    $t18 := $Dereference($t17);

    // trace_local[current_shares]($t18) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:144:17+14
    assume {:print "$track_local(55,0,6):", $t18} $t18 == $t18;

    // $t19 := 18446744073709551615 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:145:21+7
    assume {:print "$at(58,5925,5932)"} true;
    $t19 := 18446744073709551615;
    assume $IsValid'u64'($t19);

    // $t20 := -($t19, $t18) on_abort goto L14 with $t15 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:145:29+1
    call $t20 := $Sub($t19, $t18);
    if ($abort_flag) {
        assume {:print "$at(58,5933,5934)"} true;
        $t15 := $abort_code;
        assume {:print "$track_abort(55,0):", $t15} $t15 == $t15;
        goto L14;
    }

    // $t21 := >=($t20, $t2) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:145:46+2
    call $t21 := $Ge($t20, $t2);

    // if ($t21) goto L3 else goto L15 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:145:13+102
    if ($t21) { goto L3; } else { goto L15; }

    // label L3 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:145:13+102
L3:

    // goto L4 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:145:13+102
    assume {:print "$at(58,5917,6019)"} true;
    goto L4;

    // label L2 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:145:13+102
L2:

    // trace_local[pool]($t0) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:145:13+102
    assume {:print "$at(58,5917,6019)"} true;
    $temp_0'$1_pool_u64_Pool' := $Dereference($t0);
    assume {:print "$track_local(55,0,0):", $temp_0'$1_pool_u64_Pool'} $temp_0'$1_pool_u64_Pool' == $temp_0'$1_pool_u64_Pool';

    // destroy($t17) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:145:13+102

    // $t22 := 5 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:145:85+28
    $t22 := 5;
    assume $IsValid'u64'($t22);

    // $t23 := error::invalid_argument($t22) on_abort goto L14 with $t15 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:145:61+53
    call $t23 := $1_error_invalid_argument($t22);
    if ($abort_flag) {
        assume {:print "$at(58,5965,6018)"} true;
        $t15 := $abort_code;
        assume {:print "$track_abort(55,0):", $t15} $t15 == $t15;
        goto L14;
    }

    // trace_abort($t23) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:145:13+102
    assume {:print "$at(58,5917,6019)"} true;
    assume {:print "$track_abort(55,0):", $t23} $t23 == $t23;

    // $t15 := move($t23) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:145:13+102
    $t15 := $t23;

    // goto L14 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:145:13+102
    goto L14;

    // label L4 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:147:32+14
    assume {:print "$at(58,6053,6067)"} true;
L4:

    // $t24 := +($t18, $t2) on_abort goto L14 with $t15 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:147:47+1
    assume {:print "$at(58,6068,6069)"} true;
    call $t24 := $AddU64($t18, $t2);
    if ($abort_flag) {
        assume {:print "$at(58,6068,6069)"} true;
        $t15 := $abort_code;
        assume {:print "$track_abort(55,0):", $t15} $t15 == $t15;
        goto L14;
    }

    // write_ref($t17, $t24) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:147:13+46
    $t17 := $UpdateMutation($t17, $t24);

    // $t5 := read_ref($t17) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:148:13+16
    assume {:print "$at(58,6094,6110)"} true;
    $t5 := $Dereference($t17);

    // write_back[Reference($t16)[]]($t17) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:148:13+16
    $t16 := $UpdateMutation($t16, UpdateTable($Dereference($t16), ReadVec(p#$Mutation($t17), LenVec(p#$Mutation($t16))), $Dereference($t17)));

    // write_back[Reference($t0).shares (simple_map::SimpleMap<address, u64>)]($t16) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:148:13+16
    $t0 := $UpdateMutation($t0, $Update'$1_pool_u64_Pool'_shares($Dereference($t0), $Dereference($t16)));

    // trace_local[pool]($t0) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:148:13+16
    $temp_0'$1_pool_u64_Pool' := $Dereference($t0);
    assume {:print "$track_local(55,0,0):", $temp_0'$1_pool_u64_Pool'} $temp_0'$1_pool_u64_Pool' == $temp_0'$1_pool_u64_Pool';

    // goto L5 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:142:9+808
    assume {:print "$at(58,5729,6537)"} true;
    goto L5;

    // label L0 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:149:20+10
    assume {:print "$at(58,6130,6140)"} true;
L0:

    // $t25 := 0 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:149:33+1
    assume {:print "$at(58,6143,6144)"} true;
    $t25 := 0;
    assume $IsValid'u64'($t25);

    // $t26 := >($t2, $t25) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:149:31+1
    call $t26 := $Gt($t2, $t25);

    // if ($t26) goto L7 else goto L6 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:149:16+411
    if ($t26) { goto L7; } else { goto L6; }

    // label L7 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:151:33+4
    assume {:print "$at(58,6201,6205)"} true;
L7:

    // $t27 := get_field<pool_u64::Pool>.shareholders($t0) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:151:32+18
    assume {:print "$at(58,6200,6218)"} true;
    $t27 := $shareholders#$1_pool_u64_Pool($Dereference($t0));

    // $t28 := vector::length<address>($t27) on_abort goto L14 with $t15 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:151:17+34
    call $t28 := $1_vector_length'address'($t27);
    if ($abort_flag) {
        assume {:print "$at(58,6185,6219)"} true;
        $t15 := $abort_code;
        assume {:print "$track_abort(55,0):", $t15} $t15 == $t15;
        goto L14;
    }

    // $t29 := get_field<pool_u64::Pool>.shareholders_limit($t0) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:151:54+23
    $t29 := $shareholders_limit#$1_pool_u64_Pool($Dereference($t0));

    // $t30 := <($t28, $t29) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:151:52+1
    call $t30 := $Lt($t28, $t29);

    // if ($t30) goto L9 else goto L8 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:150:13+162
    assume {:print "$at(58,6160,6322)"} true;
    if ($t30) { goto L9; } else { goto L8; }

    // label L9 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:150:13+162
L9:

    // goto L10 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:150:13+162
    assume {:print "$at(58,6160,6322)"} true;
    goto L10;

    // label L8 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:150:13+162
L8:

    // pack_ref_deep($t0) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:150:13+162
    assume {:print "$at(58,6160,6322)"} true;

    // destroy($t0) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:150:13+162

    // $t31 := 2 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:152:38+22
    assume {:print "$at(58,6284,6306)"} true;
    $t31 := 2;
    assume $IsValid'u64'($t31);

    // $t32 := error::invalid_state($t31) on_abort goto L14 with $t15 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:152:17+44
    call $t32 := $1_error_invalid_state($t31);
    if ($abort_flag) {
        assume {:print "$at(58,6263,6307)"} true;
        $t15 := $abort_code;
        assume {:print "$track_abort(55,0):", $t15} $t15 == $t15;
        goto L14;
    }

    // trace_abort($t32) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:150:13+162
    assume {:print "$at(58,6160,6322)"} true;
    assume {:print "$track_abort(55,0):", $t32} $t32 == $t32;

    // $t15 := move($t32) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:150:13+162
    $t15 := $t32;

    // goto L14 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:150:13+162
    goto L14;

    // label L10 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:155:36+4
    assume {:print "$at(58,6360,6364)"} true;
L10:

    // $t33 := borrow_field<pool_u64::Pool>.shareholders($t0) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:155:31+22
    assume {:print "$at(58,6355,6377)"} true;
    $t33 := $ChildMutation($t0, 4, $shareholders#$1_pool_u64_Pool($Dereference($t0)));

    // vector::push_back<address>($t33, $t1) on_abort goto L14 with $t15 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:155:13+54
    call $t33 := $1_vector_push_back'address'($t33, $t1);
    if ($abort_flag) {
        assume {:print "$at(58,6337,6391)"} true;
        $t15 := $abort_code;
        assume {:print "$track_abort(55,0):", $t15} $t15 == $t15;
        goto L14;
    }

    // write_back[Reference($t0).shareholders (vector<address>)]($t33) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:155:13+54
    $t0 := $UpdateMutation($t0, $Update'$1_pool_u64_Pool'_shareholders($Dereference($t0), $Dereference($t33)));

    // trace_local[pool]($t0) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:155:13+54
    $temp_0'$1_pool_u64_Pool' := $Dereference($t0);
    assume {:print "$track_local(55,0,0):", $temp_0'$1_pool_u64_Pool'} $temp_0'$1_pool_u64_Pool' == $temp_0'$1_pool_u64_Pool';

    // $t34 := borrow_field<pool_u64::Pool>.shares($t0) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:156:29+16
    assume {:print "$at(58,6421,6437)"} true;
    $t34 := $ChildMutation($t0, 3, $shares#$1_pool_u64_Pool($Dereference($t0)));

    // simple_map::add<address, u64>($t34, $t1, $t2) on_abort goto L14 with $t15 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:156:13+58
    call $t34 := $1_simple_map_add'address_u64'($t34, $t1, $t2);
    if ($abort_flag) {
        assume {:print "$at(58,6405,6463)"} true;
        $t15 := $abort_code;
        assume {:print "$track_abort(55,0):", $t15} $t15 == $t15;
        goto L14;
    }

    // write_back[Reference($t0).shares (simple_map::SimpleMap<address, u64>)]($t34) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:156:13+58
    $t0 := $UpdateMutation($t0, $Update'$1_pool_u64_Pool'_shares($Dereference($t0), $Dereference($t34)));

    // trace_local[pool]($t0) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:156:13+58
    $temp_0'$1_pool_u64_Pool' := $Dereference($t0);
    assume {:print "$track_local(55,0,0):", $temp_0'$1_pool_u64_Pool'} $temp_0'$1_pool_u64_Pool' == $temp_0'$1_pool_u64_Pool';

    // goto L11 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:149:16+411
    assume {:print "$at(58,6126,6537)"} true;
    goto L11;

    // label L6 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:149:16+411
L6:

    // destroy($t0) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:149:16+411
    assume {:print "$at(58,6126,6537)"} true;

    // label L11 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:149:16+411
L11:

    // $t5 := $t2 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:142:9+808
    assume {:print "$at(58,5729,6537)"} true;
    $t5 := $t2;

    // label L5 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:142:9+808
L5:

    // trace_return[0]($t5) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:142:9+808
    assume {:print "$at(58,5729,6537)"} true;
    assume {:print "$track_return(55,0,0):", $t5} $t5 == $t5;

    // trace_local[pool]($t0) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:142:9+808
    $temp_0'$1_pool_u64_Pool' := $Dereference($t0);
    assume {:print "$track_local(55,0,0):", $temp_0'$1_pool_u64_Pool'} $temp_0'$1_pool_u64_Pool' == $temp_0'$1_pool_u64_Pool';

    // pack_ref_deep($t0) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:142:9+808

    // goto L13 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:142:9+808
    goto L13;

    // label L12 at <internal>:1:1+10
    assume {:print "$at(1,0,10)"} true;
L12:

    // destroy($t0) at <internal>:1:1+10
    assume {:print "$at(1,0,10)"} true;

    // goto L2 at <internal>:1:1+10
    goto L2;

    // label L13 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:161:5+1
    assume {:print "$at(58,6542,6543)"} true;
L13:

    // return $t5 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:161:5+1
    assume {:print "$at(58,6542,6543)"} true;
    $ret0 := $t5;
    $ret1 := $t0;
    return;

    // label L14 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:161:5+1
L14:

    // abort($t15) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:161:5+1
    assume {:print "$at(58,6542,6543)"} true;
    $abort_code := $t15;
    $abort_flag := true;
    return;

    // label L15 at <internal>:1:1+10
    assume {:print "$at(1,0,10)"} true;
L15:

    // destroy($t16) at <internal>:1:1+10
    assume {:print "$at(1,0,10)"} true;

    // goto L12 at <internal>:1:1+10
    goto L12;

}

// fun pool_u64::amount_to_shares_with_total_coins [baseline] at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:220:5+904
procedure {:inline 1} $1_pool_u64_amount_to_shares_with_total_coins(_$t0: $1_pool_u64_Pool, _$t1: int, _$t2: int) returns ($ret0: int)
{
    // declare local variables
    var $t3: bool;
    var $t4: int;
    var $t5: int;
    var $t6: int;
    var $t7: bool;
    var $t8: bool;
    var $t9: int;
    var $t10: int;
    var $t11: int;
    var $t12: int;
    var $t13: int;
    var $t0: $1_pool_u64_Pool;
    var $t1: int;
    var $t2: int;
    var $temp_0'$1_pool_u64_Pool': $1_pool_u64_Pool;
    var $temp_0'u64': int;
    $t0 := _$t0;
    $t1 := _$t1;
    $t2 := _$t2;

    // bytecode translation starts here
    // trace_local[pool]($t0) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:220:5+1
    assume {:print "$at(58,9317,9318)"} true;
    assume {:print "$track_local(55,2,0):", $t0} $t0 == $t0;

    // trace_local[coins_amount]($t1) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:220:5+1
    assume {:print "$track_local(55,2,1):", $t1} $t1 == $t1;

    // trace_local[total_coins]($t2) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:220:5+1
    assume {:print "$track_local(55,2,2):", $t2} $t2 == $t2;

    // $t5 := get_field<pool_u64::Pool>.total_coins($t0) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:222:13+16
    assume {:print "$at(58,9502,9518)"} true;
    $t5 := $total_coins#$1_pool_u64_Pool($t0);

    // $t6 := 0 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:222:33+1
    $t6 := 0;
    assume $IsValid'u64'($t6);

    // $t7 := ==($t5, $t6) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:222:30+2
    $t7 := $IsEqual'u64'($t5, $t6);

    // if ($t7) goto L1 else goto L0 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:222:13+47
    if ($t7) { goto L1; } else { goto L0; }

    // label L1 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:222:13+47
L1:

    // $t8 := true at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:222:13+47
    assume {:print "$at(58,9502,9549)"} true;
    $t8 := true;
    assume $IsValid'bool'($t8);

    // $t3 := $t8 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:222:13+47
    $t3 := $t8;

    // goto L2 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:222:13+47
    goto L2;

    // label L0 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:222:38+4
L0:

    // $t9 := get_field<pool_u64::Pool>.total_shares($t0) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:222:38+17
    assume {:print "$at(58,9527,9544)"} true;
    $t9 := $total_shares#$1_pool_u64_Pool($t0);

    // $t10 := 0 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:222:59+1
    $t10 := 0;
    assume $IsValid'u64'($t10);

    // $t3 := ==($t9, $t10) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:222:56+2
    $t3 := $IsEqual'u64'($t9, $t10);

    // label L2 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:222:13+47
L2:

    // if ($t3) goto L4 else goto L3 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:222:9+717
    assume {:print "$at(58,9498,10215)"} true;
    if ($t3) { goto L4; } else { goto L3; }

    // label L4 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:225:13+12
    assume {:print "$at(58,9800,9812)"} true;
L4:

    // $t11 := get_field<pool_u64::Pool>.scaling_factor($t0) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:225:28+19
    assume {:print "$at(58,9815,9834)"} true;
    $t11 := $scaling_factor#$1_pool_u64_Pool($t0);

    // $t4 := *($t1, $t11) on_abort goto L7 with $t12 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:225:26+1
    call $t4 := $MulU64($t1, $t11);
    if ($abort_flag) {
        assume {:print "$at(58,9813,9814)"} true;
        $t12 := $abort_code;
        assume {:print "$track_abort(55,2):", $t12} $t12 == $t12;
        goto L7;
    }

    // goto L5 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:222:9+717
    assume {:print "$at(58,9498,10215)"} true;
    goto L5;

    // label L3 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:230:34+4
    assume {:print "$at(58,10154,10158)"} true;
L3:

    // $t13 := get_field<pool_u64::Pool>.total_shares($t0) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:230:54+17
    assume {:print "$at(58,10174,10191)"} true;
    $t13 := $total_shares#$1_pool_u64_Pool($t0);

    // $t4 := pool_u64::multiply_then_divide($t0, $t1, $t13, $t2) on_abort goto L7 with $t12 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:230:13+72
    call $t4 := $1_pool_u64_multiply_then_divide($t0, $t1, $t13, $t2);
    if ($abort_flag) {
        assume {:print "$at(58,10133,10205)"} true;
        $t12 := $abort_code;
        assume {:print "$track_abort(55,2):", $t12} $t12 == $t12;
        goto L7;
    }

    // label L5 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:222:9+717
    assume {:print "$at(58,9498,10215)"} true;
L5:

    // trace_return[0]($t4) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:222:9+717
    assume {:print "$at(58,9498,10215)"} true;
    assume {:print "$track_return(55,2,0):", $t4} $t4 == $t4;

    // label L6 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:232:5+1
    assume {:print "$at(58,10220,10221)"} true;
L6:

    // return $t4 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:232:5+1
    assume {:print "$at(58,10220,10221)"} true;
    $ret0 := $t4;
    return;

    // label L7 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:232:5+1
L7:

    // abort($t12) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:232:5+1
    assume {:print "$at(58,10220,10221)"} true;
    $abort_code := $t12;
    $abort_flag := true;
    return;

}

// fun pool_u64::total_coins [baseline] at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:81:5+73
procedure {:inline 1} $1_pool_u64_total_coins(_$t0: $1_pool_u64_Pool) returns ($ret0: int)
{
    // declare local variables
    var $t1: int;
    var $t0: $1_pool_u64_Pool;
    var $temp_0'$1_pool_u64_Pool': $1_pool_u64_Pool;
    var $temp_0'u64': int;
    $t0 := _$t0;

    // bytecode translation starts here
    // trace_local[pool]($t0) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:81:5+1
    assume {:print "$at(58,3352,3353)"} true;
    assume {:print "$track_local(55,18,0):", $t0} $t0 == $t0;

    // $t1 := get_field<pool_u64::Pool>.total_coins($t0) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:82:9+16
    assume {:print "$at(58,3403,3419)"} true;
    $t1 := $total_coins#$1_pool_u64_Pool($t0);

    // trace_return[0]($t1) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:82:9+16
    assume {:print "$track_return(55,18,0):", $t1} $t1 == $t1;

    // label L1 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:83:5+1
    assume {:print "$at(58,3424,3425)"} true;
L1:

    // return $t1 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:83:5+1
    assume {:print "$at(58,3424,3425)"} true;
    $ret0 := $t1;
    return;

}

// fun pool_u64::deduct_shares [baseline] at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:194:5+857
procedure {:inline 1} $1_pool_u64_deduct_shares(_$t0: $Mutation ($1_pool_u64_Pool), _$t1: int, _$t2: int) returns ($ret0: int, $ret1: $Mutation ($1_pool_u64_Pool))
{
    // declare local variables
    var $t3: int;
    var $t4: int;
    var $t5: $Mutation (int);
    var $t6: int;
    var $t7: int;
    var $t8: int;
    var $t9: int;
    var $t10: $1_pool_u64_Pool;
    var $t11: bool;
    var $t12: int;
    var $t13: int;
    var $t14: int;
    var $t15: $1_pool_u64_Pool;
    var $t16: int;
    var $t17: bool;
    var $t18: int;
    var $t19: int;
    var $t20: $Mutation (Table int (int));
    var $t21: $Mutation (int);
    var $t22: int;
    var $t23: int;
    var $t24: int;
    var $t25: int;
    var $t26: bool;
    var $t27: Vec (int);
    var $t28: bool;
    var $t29: int;
    var $t30: $Mutation (Vec (int));
    var $t31: int;
    var $t32: $Mutation (Table int (int));
    var $t33: int;
    var $t34: int;
    var $t0: $Mutation ($1_pool_u64_Pool);
    var $t1: int;
    var $t2: int;
    var $temp_0'$1_pool_u64_Pool': $1_pool_u64_Pool;
    var $temp_0'address': int;
    var $temp_0'u64': int;
    $t0 := _$t0;
    $t1 := _$t1;
    $t2 := _$t2;

    // bytecode translation starts here
    // assume Identical($t8, Sub(simple_map::spec_get<address, u64>(select pool_u64::Pool.shares($t0), $t1), $t2)) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.spec.move:173:9+83
    assume {:print "$at(59,7278,7361)"} true;
    assume ($t8 == ($1_simple_map_spec_get'address_u64'($shares#$1_pool_u64_Pool($Dereference($t0)), $t1) - $t2));

    // assume Identical($t9, Sub(simple_map::spec_get<address, u64>(select pool_u64::Pool.shares($t0), $t1), $t2)) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.spec.move:181:9+83
    assume {:print "$at(59,7643,7726)"} true;
    assume ($t9 == ($1_simple_map_spec_get'address_u64'($shares#$1_pool_u64_Pool($Dereference($t0)), $t1) - $t2));

    // trace_local[pool]($t0) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:194:5+1
    assume {:print "$at(58,7989,7990)"} true;
    $temp_0'$1_pool_u64_Pool' := $Dereference($t0);
    assume {:print "$track_local(55,8,0):", $temp_0'$1_pool_u64_Pool'} $temp_0'$1_pool_u64_Pool' == $temp_0'$1_pool_u64_Pool';

    // trace_local[shareholder]($t1) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:194:5+1
    assume {:print "$track_local(55,8,1):", $t1} $t1 == $t1;

    // trace_local[num_shares]($t2) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:194:5+1
    assume {:print "$track_local(55,8,2):", $t2} $t2 == $t2;

    // $t10 := read_ref($t0) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:195:25+19
    assume {:print "$at(58,8094,8113)"} true;
    $t10 := $Dereference($t0);

    // $t11 := pool_u64::contains($t10, $t1) on_abort goto L10 with $t12 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:195:17+27
    call $t11 := $1_pool_u64_contains($t10, $t1);
    if ($abort_flag) {
        assume {:print "$at(58,8086,8113)"} true;
        $t12 := $abort_code;
        assume {:print "$track_abort(55,8):", $t12} $t12 == $t12;
        goto L10;
    }

    // if ($t11) goto L1 else goto L0 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:195:9+85
    if ($t11) { goto L1; } else { goto L0; }

    // label L1 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:195:9+85
L1:

    // goto L2 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:195:9+85
    assume {:print "$at(58,8078,8163)"} true;
    goto L2;

    // label L0 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:195:9+85
L0:

    // pack_ref_deep($t0) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:195:9+85
    assume {:print "$at(58,8078,8163)"} true;

    // destroy($t0) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:195:9+85

    // $t13 := 1 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:195:70+22
    $t13 := 1;
    assume $IsValid'u64'($t13);

    // $t14 := error::invalid_argument($t13) on_abort goto L10 with $t12 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:195:46+47
    call $t14 := $1_error_invalid_argument($t13);
    if ($abort_flag) {
        assume {:print "$at(58,8115,8162)"} true;
        $t12 := $abort_code;
        assume {:print "$track_abort(55,8):", $t12} $t12 == $t12;
        goto L10;
    }

    // trace_abort($t14) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:195:9+85
    assume {:print "$at(58,8078,8163)"} true;
    assume {:print "$track_abort(55,8):", $t14} $t14 == $t14;

    // $t12 := move($t14) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:195:9+85
    $t12 := $t14;

    // goto L10 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:195:9+85
    goto L10;

    // label L2 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:196:24+4
    assume {:print "$at(58,8188,8192)"} true;
L2:

    // $t15 := read_ref($t0) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:196:23+19
    assume {:print "$at(58,8187,8206)"} true;
    $t15 := $Dereference($t0);

    // $t16 := pool_u64::shares($t15, $t1) on_abort goto L10 with $t12 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:196:17+25
    call $t16 := $1_pool_u64_shares($t15, $t1);
    if ($abort_flag) {
        assume {:print "$at(58,8181,8206)"} true;
        $t12 := $abort_code;
        assume {:print "$track_abort(55,8):", $t12} $t12 == $t12;
        goto L10;
    }

    // $t17 := >=($t16, $t2) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:196:43+2
    call $t17 := $Ge($t16, $t2);

    // if ($t17) goto L4 else goto L3 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:196:9+95
    if ($t17) { goto L4; } else { goto L3; }

    // label L4 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:196:9+95
L4:

    // goto L5 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:196:9+95
    assume {:print "$at(58,8173,8268)"} true;
    goto L5;

    // label L3 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:196:9+95
L3:

    // pack_ref_deep($t0) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:196:9+95
    assume {:print "$at(58,8173,8268)"} true;

    // destroy($t0) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:196:9+95

    // $t18 := 4 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:196:82+20
    $t18 := 4;
    assume $IsValid'u64'($t18);

    // $t19 := error::invalid_argument($t18) on_abort goto L10 with $t12 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:196:58+45
    call $t19 := $1_error_invalid_argument($t18);
    if ($abort_flag) {
        assume {:print "$at(58,8222,8267)"} true;
        $t12 := $abort_code;
        assume {:print "$track_abort(55,8):", $t12} $t12 == $t12;
        goto L10;
    }

    // trace_abort($t19) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:196:9+95
    assume {:print "$at(58,8173,8268)"} true;
    assume {:print "$track_abort(55,8):", $t19} $t19 == $t19;

    // $t12 := move($t19) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:196:9+95
    $t12 := $t19;

    // goto L10 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:196:9+95
    goto L10;

    // label L5 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:198:59+4
    assume {:print "$at(58,8329,8333)"} true;
L5:

    // $t20 := borrow_field<pool_u64::Pool>.shares($t0) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:198:54+16
    assume {:print "$at(58,8324,8340)"} true;
    $t20 := $ChildMutation($t0, 3, $shares#$1_pool_u64_Pool($Dereference($t0)));

    // $t21 := simple_map::borrow_mut<address, u64>($t20, $t1) on_abort goto L10 with $t12 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:198:31+54
    call $t21,$t20 := $1_simple_map_borrow_mut'address_u64'($t20, $t1);
    if ($abort_flag) {
        assume {:print "$at(58,8301,8355)"} true;
        $t12 := $abort_code;
        assume {:print "$track_abort(55,8):", $t12} $t12 == $t12;
        goto L10;
    }

    // trace_local[existing_shares]($t21) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:198:13+15
    $temp_0'u64' := $Dereference($t21);
    assume {:print "$track_local(55,8,5):", $temp_0'u64'} $temp_0'u64' == $temp_0'u64';

    // $t22 := read_ref($t21) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:199:28+16
    assume {:print "$at(58,8384,8400)"} true;
    $t22 := $Dereference($t21);

    // $t23 := -($t22, $t2) on_abort goto L10 with $t12 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:199:45+1
    call $t23 := $Sub($t22, $t2);
    if ($abort_flag) {
        assume {:print "$at(58,8401,8402)"} true;
        $t12 := $abort_code;
        assume {:print "$track_abort(55,8):", $t12} $t12 == $t12;
        goto L10;
    }

    // write_ref($t21, $t23) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:199:9+48
    $t21 := $UpdateMutation($t21, $t23);

    // $t24 := read_ref($t21) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:202:32+16
    assume {:print "$at(58,8521,8537)"} true;
    $t24 := $Dereference($t21);

    // write_back[Reference($t20)[]]($t21) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:202:32+16
    $t20 := $UpdateMutation($t20, UpdateTable($Dereference($t20), ReadVec(p#$Mutation($t21), LenVec(p#$Mutation($t20))), $Dereference($t21)));

    // write_back[Reference($t0).shares (simple_map::SimpleMap<address, u64>)]($t20) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:202:32+16
    $t0 := $UpdateMutation($t0, $Update'$1_pool_u64_Pool'_shares($Dereference($t0), $Dereference($t20)));

    // trace_local[pool]($t0) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:202:32+16
    $temp_0'$1_pool_u64_Pool' := $Dereference($t0);
    assume {:print "$track_local(55,8,0):", $temp_0'$1_pool_u64_Pool'} $temp_0'$1_pool_u64_Pool' == $temp_0'$1_pool_u64_Pool';

    // trace_local[remaining_shares]($t24) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:202:13+16
    assume {:print "$track_local(55,8,6):", $t24} $t24 == $t24;

    // $t25 := 0 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:203:33+1
    assume {:print "$at(58,8571,8572)"} true;
    $t25 := 0;
    assume $IsValid'u64'($t25);

    // $t26 := ==($t24, $t25) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:203:30+2
    $t26 := $IsEqual'u64'($t24, $t25);

    // if ($t26) goto L7 else goto L6 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:203:9+266
    if ($t26) { goto L7; } else { goto L6; }

    // label L7 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:204:60+4
    assume {:print "$at(58,8635,8639)"} true;
L7:

    // $t27 := get_field<pool_u64::Pool>.shareholders($t0) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:204:59+18
    assume {:print "$at(58,8634,8652)"} true;
    $t27 := $shareholders#$1_pool_u64_Pool($Dereference($t0));

    // ($t28, $t29) := vector::index_of<address>($t27, $t1) on_abort goto L10 with $t12 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:204:42+50
    call $t28,$t29 := $1_vector_index_of'address'($t27, $t1);
    if ($abort_flag) {
        assume {:print "$at(58,8617,8667)"} true;
        $t12 := $abort_code;
        assume {:print "$track_abort(55,8):", $t12} $t12 == $t12;
        goto L10;
    }

    // trace_local[shareholder_index]($t29) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:204:21+17
    assume {:print "$track_local(55,8,7):", $t29} $t29 == $t29;

    // destroy($t28) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:204:18+1

    // $t30 := borrow_field<pool_u64::Pool>.shareholders($t0) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:205:28+22
    assume {:print "$at(58,8696,8718)"} true;
    $t30 := $ChildMutation($t0, 4, $shareholders#$1_pool_u64_Pool($Dereference($t0)));

    // $t31 := vector::remove<address>($t30, $t29) on_abort goto L10 with $t12 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:205:13+57
    call $t31,$t30 := $1_vector_remove'address'($t30, $t29);
    if ($abort_flag) {
        assume {:print "$at(58,8681,8738)"} true;
        $t12 := $abort_code;
        assume {:print "$track_abort(55,8):", $t12} $t12 == $t12;
        goto L10;
    }

    // write_back[Reference($t0).shareholders (vector<address>)]($t30) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:205:13+57
    $t0 := $UpdateMutation($t0, $Update'$1_pool_u64_Pool'_shareholders($Dereference($t0), $Dereference($t30)));

    // trace_local[pool]($t0) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:205:13+57
    $temp_0'$1_pool_u64_Pool' := $Dereference($t0);
    assume {:print "$track_local(55,8,0):", $temp_0'$1_pool_u64_Pool'} $temp_0'$1_pool_u64_Pool' == $temp_0'$1_pool_u64_Pool';

    // destroy($t31) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:205:13+57

    // $t32 := borrow_field<pool_u64::Pool>.shares($t0) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:206:32+16
    assume {:print "$at(58,8771,8787)"} true;
    $t32 := $ChildMutation($t0, 3, $shares#$1_pool_u64_Pool($Dereference($t0)));

    // ($t33, $t34) := simple_map::remove<address, u64>($t32, $t1) on_abort goto L10 with $t12 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:206:13+50
    call $t33,$t34,$t32 := $1_simple_map_remove'address_u64'($t32, $t1);
    if ($abort_flag) {
        assume {:print "$at(58,8752,8802)"} true;
        $t12 := $abort_code;
        assume {:print "$track_abort(55,8):", $t12} $t12 == $t12;
        goto L10;
    }

    // write_back[Reference($t0).shares (simple_map::SimpleMap<address, u64>)]($t32) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:206:13+50
    $t0 := $UpdateMutation($t0, $Update'$1_pool_u64_Pool'_shares($Dereference($t0), $Dereference($t32)));

    // trace_local[pool]($t0) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:206:13+50
    $temp_0'$1_pool_u64_Pool' := $Dereference($t0);
    assume {:print "$track_local(55,8,0):", $temp_0'$1_pool_u64_Pool'} $temp_0'$1_pool_u64_Pool' == $temp_0'$1_pool_u64_Pool';

    // destroy($t34) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:206:13+50

    // destroy($t33) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:206:13+50

    // goto L8 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:206:63+1
    goto L8;

    // label L6 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:203:9+266
    assume {:print "$at(58,8547,8813)"} true;
L6:

    // destroy($t0) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:203:9+266
    assume {:print "$at(58,8547,8813)"} true;

    // label L8 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:209:9+16
    assume {:print "$at(58,8824,8840)"} true;
L8:

    // trace_return[0]($t24) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:209:9+16
    assume {:print "$at(58,8824,8840)"} true;
    assume {:print "$track_return(55,8,0):", $t24} $t24 == $t24;

    // trace_local[pool]($t0) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:209:9+16
    $temp_0'$1_pool_u64_Pool' := $Dereference($t0);
    assume {:print "$track_local(55,8,0):", $temp_0'$1_pool_u64_Pool'} $temp_0'$1_pool_u64_Pool' == $temp_0'$1_pool_u64_Pool';

    // pack_ref_deep($t0) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:209:9+16

    // label L9 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:210:5+1
    assume {:print "$at(58,8845,8846)"} true;
L9:

    // return $t24 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:210:5+1
    assume {:print "$at(58,8845,8846)"} true;
    $ret0 := $t24;
    $ret1 := $t0;
    return;

    // label L10 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:210:5+1
L10:

    // abort($t12) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:210:5+1
    assume {:print "$at(58,8845,8846)"} true;
    $abort_code := $t12;
    $abort_flag := true;
    return;

}

// fun pool_u64::multiply_then_divide [baseline] at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:254:5+167
procedure {:inline 1} $1_pool_u64_multiply_then_divide(_$t0: $1_pool_u64_Pool, _$t1: int, _$t2: int, _$t3: int) returns ($ret0: int)
{
    // declare local variables
    var $t4: int;
    var $t5: int;
    var $t6: int;
    var $t7: int;
    var $t8: int;
    var $t9: int;
    var $t10: int;
    var $t0: $1_pool_u64_Pool;
    var $t1: int;
    var $t2: int;
    var $t3: int;
    var $temp_0'$1_pool_u64_Pool': $1_pool_u64_Pool;
    var $temp_0'u64': int;
    $t0 := _$t0;
    $t1 := _$t1;
    $t2 := _$t2;
    $t3 := _$t3;

    // bytecode translation starts here
    // trace_local[_pool]($t0) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:254:5+1
    assume {:print "$at(58,11269,11270)"} true;
    assume {:print "$track_local(55,10,0):", $t0} $t0 == $t0;

    // trace_local[x]($t1) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:254:5+1
    assume {:print "$track_local(55,10,1):", $t1} $t1 == $t1;

    // trace_local[y]($t2) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:254:5+1
    assume {:print "$track_local(55,10,2):", $t2} $t2 == $t2;

    // trace_local[z]($t3) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:254:5+1
    assume {:print "$track_local(55,10,3):", $t3} $t3 == $t3;

    // $t4 := pool_u64::to_u128($t1) on_abort goto L2 with $t5 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:255:23+10
    assume {:print "$at(58,11368,11378)"} true;
    call $t4 := $1_pool_u64_to_u128($t1);
    if ($abort_flag) {
        assume {:print "$at(58,11368,11378)"} true;
        $t5 := $abort_code;
        assume {:print "$track_abort(55,10):", $t5} $t5 == $t5;
        goto L2;
    }

    // $t6 := pool_u64::to_u128($t2) on_abort goto L2 with $t5 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:255:36+10
    call $t6 := $1_pool_u64_to_u128($t2);
    if ($abort_flag) {
        assume {:print "$at(58,11381,11391)"} true;
        $t5 := $abort_code;
        assume {:print "$track_abort(55,10):", $t5} $t5 == $t5;
        goto L2;
    }

    // $t7 := *($t4, $t6) on_abort goto L2 with $t5 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:255:34+1
    call $t7 := $MulU128($t4, $t6);
    if ($abort_flag) {
        assume {:print "$at(58,11379,11380)"} true;
        $t5 := $abort_code;
        assume {:print "$track_abort(55,10):", $t5} $t5 == $t5;
        goto L2;
    }

    // $t8 := pool_u64::to_u128($t3) on_abort goto L2 with $t5 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:255:50+10
    call $t8 := $1_pool_u64_to_u128($t3);
    if ($abort_flag) {
        assume {:print "$at(58,11395,11405)"} true;
        $t5 := $abort_code;
        assume {:print "$track_abort(55,10):", $t5} $t5 == $t5;
        goto L2;
    }

    // $t9 := /($t7, $t8) on_abort goto L2 with $t5 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:255:48+1
    call $t9 := $Div($t7, $t8);
    if ($abort_flag) {
        assume {:print "$at(58,11393,11394)"} true;
        $t5 := $abort_code;
        assume {:print "$track_abort(55,10):", $t5} $t5 == $t5;
        goto L2;
    }

    // $t10 := (u64)($t9) on_abort goto L2 with $t5 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:256:9+15
    assume {:print "$at(58,11415,11430)"} true;
    call $t10 := $CastU64($t9);
    if ($abort_flag) {
        assume {:print "$at(58,11415,11430)"} true;
        $t5 := $abort_code;
        assume {:print "$track_abort(55,10):", $t5} $t5 == $t5;
        goto L2;
    }

    // trace_return[0]($t10) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:256:9+15
    assume {:print "$track_return(55,10,0):", $t10} $t10 == $t10;

    // label L1 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:257:5+1
    assume {:print "$at(58,11435,11436)"} true;
L1:

    // return $t10 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:257:5+1
    assume {:print "$at(58,11435,11436)"} true;
    $ret0 := $t10;
    return;

    // label L2 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:257:5+1
L2:

    // abort($t5) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:257:5+1
    assume {:print "$at(58,11435,11436)"} true;
    $abort_code := $t5;
    $abort_flag := true;
    return;

}

// fun pool_u64::shareholders [baseline] at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:111:5+87
procedure {:inline 1} $1_pool_u64_shareholders(_$t0: $1_pool_u64_Pool) returns ($ret0: Vec (int))
{
    // declare local variables
    var $t1: Vec (int);
    var $t0: $1_pool_u64_Pool;
    var $temp_0'$1_pool_u64_Pool': $1_pool_u64_Pool;
    var $temp_0'vec'address'': Vec (int);
    $t0 := _$t0;

    // bytecode translation starts here
    // trace_local[pool]($t0) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:111:5+1
    assume {:print "$at(58,4336,4337)"} true;
    assume {:print "$track_local(55,12,0):", $t0} $t0 == $t0;

    // $t1 := get_field<pool_u64::Pool>.shareholders($t0) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:112:9+17
    assume {:print "$at(58,4400,4417)"} true;
    $t1 := $shareholders#$1_pool_u64_Pool($t0);

    // trace_return[0]($t1) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:112:9+17
    assume {:print "$track_return(55,12,0):", $t1} $t1 == $t1;

    // label L1 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:113:5+1
    assume {:print "$at(58,4422,4423)"} true;
L1:

    // return $t1 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:113:5+1
    assume {:print "$at(58,4422,4423)"} true;
    $ret0 := $t1;
    return;

}

// fun pool_u64::shares [baseline] at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:96:5+209
procedure {:inline 1} $1_pool_u64_shares(_$t0: $1_pool_u64_Pool, _$t1: int) returns ($ret0: int)
{
    // declare local variables
    var $t2: int;
    var $t3: bool;
    var $t4: int;
    var $t5: Table int (int);
    var $t6: int;
    var $t0: $1_pool_u64_Pool;
    var $t1: int;
    var $temp_0'$1_pool_u64_Pool': $1_pool_u64_Pool;
    var $temp_0'address': int;
    var $temp_0'u64': int;
    $t0 := _$t0;
    $t1 := _$t1;

    // bytecode translation starts here
    // trace_local[pool]($t0) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:96:5+1
    assume {:print "$at(58,3839,3840)"} true;
    assume {:print "$track_local(55,14,0):", $t0} $t0 == $t0;

    // trace_local[shareholder]($t1) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:96:5+1
    assume {:print "$track_local(55,14,1):", $t1} $t1 == $t1;

    // $t3 := pool_u64::contains($t0, $t1) on_abort goto L4 with $t4 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:97:13+27
    assume {:print "$at(58,3911,3938)"} true;
    call $t3 := $1_pool_u64_contains($t0, $t1);
    if ($abort_flag) {
        assume {:print "$at(58,3911,3938)"} true;
        $t4 := $abort_code;
        assume {:print "$track_abort(55,14):", $t4} $t4 == $t4;
        goto L4;
    }

    // if ($t3) goto L1 else goto L0 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:97:9+135
    if ($t3) { goto L1; } else { goto L0; }

    // label L1 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:98:34+4
    assume {:print "$at(58,3975,3979)"} true;
L1:

    // $t5 := get_field<pool_u64::Pool>.shares($t0) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:98:33+12
    assume {:print "$at(58,3974,3986)"} true;
    $t5 := $shares#$1_pool_u64_Pool($t0);

    // $t2 := simple_map::borrow<address, u64>($t5, $t1) on_abort goto L4 with $t4 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:98:14+46
    call $t2 := $1_simple_map_borrow'address_u64'($t5, $t1);
    if ($abort_flag) {
        assume {:print "$at(58,3955,4001)"} true;
        $t4 := $abort_code;
        assume {:print "$track_abort(55,14):", $t4} $t4 == $t4;
        goto L4;
    }

    // goto L2 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:97:9+135
    assume {:print "$at(58,3907,4042)"} true;
    goto L2;

    // label L0 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:97:9+135
L0:

    // $t6 := 0 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:100:13+1
    assume {:print "$at(58,4031,4032)"} true;
    $t6 := 0;
    assume $IsValid'u64'($t6);

    // $t2 := $t6 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:97:9+135
    assume {:print "$at(58,3907,4042)"} true;
    $t2 := $t6;

    // label L2 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:97:9+135
L2:

    // trace_return[0]($t2) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:97:9+135
    assume {:print "$at(58,3907,4042)"} true;
    assume {:print "$track_return(55,14,0):", $t2} $t2 == $t2;

    // label L3 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:102:5+1
    assume {:print "$at(58,4047,4048)"} true;
L3:

    // return $t2 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:102:5+1
    assume {:print "$at(58,4047,4048)"} true;
    $ret0 := $t2;
    return;

    // label L4 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:102:5+1
L4:

    // abort($t4) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:102:5+1
    assume {:print "$at(58,4047,4048)"} true;
    $abort_code := $t4;
    $abort_flag := true;
    return;

}

// fun pool_u64::shares_to_amount [baseline] at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:236:5+140
procedure {:inline 1} $1_pool_u64_shares_to_amount(_$t0: $1_pool_u64_Pool, _$t1: int) returns ($ret0: int)
{
    // declare local variables
    var $t2: int;
    var $t3: int;
    var $t4: int;
    var $t0: $1_pool_u64_Pool;
    var $t1: int;
    var $temp_0'$1_pool_u64_Pool': $1_pool_u64_Pool;
    var $temp_0'u64': int;
    $t0 := _$t0;
    $t1 := _$t1;

    // bytecode translation starts here
    // trace_local[pool]($t0) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:236:5+1
    assume {:print "$at(58,10355,10356)"} true;
    assume {:print "$track_local(55,15,0):", $t0} $t0 == $t0;

    // trace_local[shares]($t1) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:236:5+1
    assume {:print "$track_local(55,15,1):", $t1} $t1 == $t1;

    // $t2 := get_field<pool_u64::Pool>.total_coins($t0) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:237:57+16
    assume {:print "$at(58,10472,10488)"} true;
    $t2 := $total_coins#$1_pool_u64_Pool($t0);

    // $t3 := pool_u64::shares_to_amount_with_total_coins($t0, $t1, $t2) on_abort goto L2 with $t4 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:237:9+65
    call $t3 := $1_pool_u64_shares_to_amount_with_total_coins($t0, $t1, $t2);
    if ($abort_flag) {
        assume {:print "$at(58,10424,10489)"} true;
        $t4 := $abort_code;
        assume {:print "$track_abort(55,15):", $t4} $t4 == $t4;
        goto L2;
    }

    // trace_return[0]($t3) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:237:9+65
    assume {:print "$track_return(55,15,0):", $t3} $t3 == $t3;

    // label L1 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:238:5+1
    assume {:print "$at(58,10494,10495)"} true;
L1:

    // return $t3 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:238:5+1
    assume {:print "$at(58,10494,10495)"} true;
    $ret0 := $t3;
    return;

    // label L2 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:238:5+1
L2:

    // abort($t4) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:238:5+1
    assume {:print "$at(58,10494,10495)"} true;
    $abort_code := $t4;
    $abort_flag := true;
    return;

}

// fun pool_u64::shares_to_amount_with_total_coins [baseline] at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:242:5+601
procedure {:inline 1} $1_pool_u64_shares_to_amount_with_total_coins(_$t0: $1_pool_u64_Pool, _$t1: int, _$t2: int) returns ($ret0: int)
{
    // declare local variables
    var $t3: bool;
    var $t4: int;
    var $t5: int;
    var $t6: int;
    var $t7: bool;
    var $t8: bool;
    var $t9: int;
    var $t10: int;
    var $t11: int;
    var $t12: int;
    var $t13: int;
    var $t0: $1_pool_u64_Pool;
    var $t1: int;
    var $t2: int;
    var $temp_0'$1_pool_u64_Pool': $1_pool_u64_Pool;
    var $temp_0'u64': int;
    $t0 := _$t0;
    $t1 := _$t1;
    $t2 := _$t2;

    // bytecode translation starts here
    // trace_local[pool]($t0) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:242:5+1
    assume {:print "$at(58,10662,10663)"} true;
    assume {:print "$track_local(55,16,0):", $t0} $t0 == $t0;

    // trace_local[shares]($t1) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:242:5+1
    assume {:print "$track_local(55,16,1):", $t1} $t1 == $t1;

    // trace_local[total_coins]($t2) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:242:5+1
    assume {:print "$track_local(55,16,2):", $t2} $t2 == $t2;

    // $t5 := get_field<pool_u64::Pool>.total_coins($t0) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:244:13+16
    assume {:print "$at(58,10829,10845)"} true;
    $t5 := $total_coins#$1_pool_u64_Pool($t0);

    // $t6 := 0 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:244:33+1
    $t6 := 0;
    assume $IsValid'u64'($t6);

    // $t7 := ==($t5, $t6) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:244:30+2
    $t7 := $IsEqual'u64'($t5, $t6);

    // if ($t7) goto L1 else goto L0 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:244:13+47
    if ($t7) { goto L1; } else { goto L0; }

    // label L1 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:244:13+47
L1:

    // $t8 := true at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:244:13+47
    assume {:print "$at(58,10829,10876)"} true;
    $t8 := true;
    assume $IsValid'bool'($t8);

    // $t3 := $t8 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:244:13+47
    $t3 := $t8;

    // goto L2 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:244:13+47
    goto L2;

    // label L0 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:244:38+4
L0:

    // $t9 := get_field<pool_u64::Pool>.total_shares($t0) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:244:38+17
    assume {:print "$at(58,10854,10871)"} true;
    $t9 := $total_shares#$1_pool_u64_Pool($t0);

    // $t10 := 0 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:244:59+1
    $t10 := 0;
    assume $IsValid'u64'($t10);

    // $t3 := ==($t9, $t10) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:244:56+2
    $t3 := $IsEqual'u64'($t9, $t10);

    // label L2 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:244:13+47
L2:

    // if ($t3) goto L4 else goto L3 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:244:9+432
    assume {:print "$at(58,10825,11257)"} true;
    if ($t3) { goto L4; } else { goto L3; }

    // label L4 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:244:9+432
L4:

    // $t11 := 0 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:245:13+1
    assume {:print "$at(58,10892,10893)"} true;
    $t11 := 0;
    assume $IsValid'u64'($t11);

    // $t4 := $t11 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:244:9+432
    assume {:print "$at(58,10825,11257)"} true;
    $t4 := $t11;

    // goto L5 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:244:9+432
    goto L5;

    // label L3 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:250:34+4
    assume {:print "$at(58,11202,11206)"} true;
L3:

    // $t12 := get_field<pool_u64::Pool>.total_shares($t0) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:250:61+17
    assume {:print "$at(58,11229,11246)"} true;
    $t12 := $total_shares#$1_pool_u64_Pool($t0);

    // $t4 := pool_u64::multiply_then_divide($t0, $t1, $t2, $t12) on_abort goto L7 with $t13 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:250:13+66
    call $t4 := $1_pool_u64_multiply_then_divide($t0, $t1, $t2, $t12);
    if ($abort_flag) {
        assume {:print "$at(58,11181,11247)"} true;
        $t13 := $abort_code;
        assume {:print "$track_abort(55,16):", $t13} $t13 == $t13;
        goto L7;
    }

    // label L5 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:244:9+432
    assume {:print "$at(58,10825,11257)"} true;
L5:

    // trace_return[0]($t4) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:244:9+432
    assume {:print "$at(58,10825,11257)"} true;
    assume {:print "$track_return(55,16,0):", $t4} $t4 == $t4;

    // label L6 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:252:5+1
    assume {:print "$at(58,11262,11263)"} true;
L6:

    // return $t4 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:252:5+1
    assume {:print "$at(58,11262,11263)"} true;
    $ret0 := $t4;
    return;

    // label L7 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:252:5+1
L7:

    // abort($t13) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:252:5+1
    assume {:print "$at(58,11262,11263)"} true;
    $abort_code := $t13;
    $abort_flag := true;
    return;

}

// fun pool_u64::transfer_shares [baseline] at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:179:5+546
procedure {:inline 1} $1_pool_u64_transfer_shares(_$t0: $Mutation ($1_pool_u64_Pool), _$t1: int, _$t2: int, _$t3: int) returns ($ret0: $Mutation ($1_pool_u64_Pool))
{
    // declare local variables
    var $t4: int;
    var $t5: int;
    var $t6: $1_pool_u64_Pool;
    var $t7: bool;
    var $t8: int;
    var $t9: int;
    var $t10: int;
    var $t11: $1_pool_u64_Pool;
    var $t12: int;
    var $t13: bool;
    var $t14: int;
    var $t15: int;
    var $t16: int;
    var $t17: bool;
    var $t18: int;
    var $t19: int;
    var $t20: int;
    var $t21: bool;
    var $t22: bool;
    var $t23: int;
    var $t24: bool;
    var $t25: int;
    var $t26: int;
    var $t0: $Mutation ($1_pool_u64_Pool);
    var $t1: int;
    var $t2: int;
    var $t3: int;
    var $temp_0'$1_pool_u64_Pool': $1_pool_u64_Pool;
    var $temp_0'address': int;
    var $temp_0'u64': int;
    $t0 := _$t0;
    $t1 := _$t1;
    $t2 := _$t2;
    $t3 := _$t3;

    // bytecode translation starts here
    // trace_local[pool]($t0) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:179:5+1
    assume {:print "$at(58,7327,7328)"} true;
    $temp_0'$1_pool_u64_Pool' := $Dereference($t0);
    assume {:print "$track_local(55,20,0):", $temp_0'$1_pool_u64_Pool'} $temp_0'$1_pool_u64_Pool' == $temp_0'$1_pool_u64_Pool';

    // trace_local[shareholder_1]($t1) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:179:5+1
    assume {:print "$track_local(55,20,1):", $t1} $t1 == $t1;

    // trace_local[shareholder_2]($t2) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:179:5+1
    assume {:print "$track_local(55,20,2):", $t2} $t2 == $t2;

    // trace_local[shares_to_transfer]($t3) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:179:5+1
    assume {:print "$track_local(55,20,3):", $t3} $t3 == $t3;

    // $t6 := read_ref($t0) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:185:25+21
    assume {:print "$at(58,7509,7530)"} true;
    $t6 := $Dereference($t0);

    // $t7 := pool_u64::contains($t6, $t1) on_abort goto L9 with $t8 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:185:17+29
    call $t7 := $1_pool_u64_contains($t6, $t1);
    if ($abort_flag) {
        assume {:print "$at(58,7501,7530)"} true;
        $t8 := $abort_code;
        assume {:print "$track_abort(55,20):", $t8} $t8 == $t8;
        goto L9;
    }

    // if ($t7) goto L1 else goto L0 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:185:9+87
    if ($t7) { goto L1; } else { goto L0; }

    // label L1 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:185:9+87
L1:

    // goto L2 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:185:9+87
    assume {:print "$at(58,7493,7580)"} true;
    goto L2;

    // label L0 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:185:9+87
L0:

    // pack_ref_deep($t0) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:185:9+87
    assume {:print "$at(58,7493,7580)"} true;

    // destroy($t0) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:185:9+87

    // $t9 := 1 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:185:72+22
    $t9 := 1;
    assume $IsValid'u64'($t9);

    // $t10 := error::invalid_argument($t9) on_abort goto L9 with $t8 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:185:48+47
    call $t10 := $1_error_invalid_argument($t9);
    if ($abort_flag) {
        assume {:print "$at(58,7532,7579)"} true;
        $t8 := $abort_code;
        assume {:print "$track_abort(55,20):", $t8} $t8 == $t8;
        goto L9;
    }

    // trace_abort($t10) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:185:9+87
    assume {:print "$at(58,7493,7580)"} true;
    assume {:print "$track_abort(55,20):", $t10} $t10 == $t10;

    // $t8 := move($t10) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:185:9+87
    $t8 := $t10;

    // goto L9 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:185:9+87
    goto L9;

    // label L2 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:186:24+4
    assume {:print "$at(58,7605,7609)"} true;
L2:

    // $t11 := read_ref($t0) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:186:23+21
    assume {:print "$at(58,7604,7625)"} true;
    $t11 := $Dereference($t0);

    // $t12 := pool_u64::shares($t11, $t1) on_abort goto L9 with $t8 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:186:17+27
    call $t12 := $1_pool_u64_shares($t11, $t1);
    if ($abort_flag) {
        assume {:print "$at(58,7598,7625)"} true;
        $t8 := $abort_code;
        assume {:print "$track_abort(55,20):", $t8} $t8 == $t8;
        goto L9;
    }

    // $t13 := >=($t12, $t3) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:186:45+2
    call $t13 := $Ge($t12, $t3);

    // if ($t13) goto L4 else goto L3 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:186:9+105
    if ($t13) { goto L4; } else { goto L3; }

    // label L4 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:186:9+105
L4:

    // goto L5 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:186:9+105
    assume {:print "$at(58,7590,7695)"} true;
    goto L5;

    // label L3 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:186:9+105
L3:

    // pack_ref_deep($t0) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:186:9+105
    assume {:print "$at(58,7590,7695)"} true;

    // destroy($t0) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:186:9+105

    // $t14 := 4 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:186:92+20
    $t14 := 4;
    assume $IsValid'u64'($t14);

    // $t15 := error::invalid_argument($t14) on_abort goto L9 with $t8 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:186:68+45
    call $t15 := $1_error_invalid_argument($t14);
    if ($abort_flag) {
        assume {:print "$at(58,7649,7694)"} true;
        $t8 := $abort_code;
        assume {:print "$track_abort(55,20):", $t8} $t8 == $t8;
        goto L9;
    }

    // trace_abort($t15) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:186:9+105
    assume {:print "$at(58,7590,7695)"} true;
    assume {:print "$track_abort(55,20):", $t15} $t15 == $t15;

    // $t8 := move($t15) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:186:9+105
    $t8 := $t15;

    // goto L9 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:186:9+105
    goto L9;

    // label L5 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:187:13+18
    assume {:print "$at(58,7709,7727)"} true;
L5:

    // $t16 := 0 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:187:35+1
    assume {:print "$at(58,7731,7732)"} true;
    $t16 := 0;
    assume $IsValid'u64'($t16);

    // $t17 := ==($t3, $t16) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:187:32+2
    $t17 := $IsEqual'u64'($t3, $t16);

    // if ($t17) goto L7 else goto L6 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:187:9+35
    if ($t17) { goto L7; } else { goto L6; }

    // label L7 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:187:38+6
L7:

    // destroy($t0) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:187:38+6
    assume {:print "$at(58,7734,7740)"} true;

    // trace_local[pool]($t0) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:187:38+6
    $temp_0'$1_pool_u64_Pool' := $Dereference($t0);
    assume {:print "$track_local(55,20,0):", $temp_0'$1_pool_u64_Pool'} $temp_0'$1_pool_u64_Pool' == $temp_0'$1_pool_u64_Pool';

    // pack_ref_deep($t0) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:187:38+6

    // goto L8 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:187:38+6
    goto L8;

    // label L6 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:189:23+4
    assume {:print "$at(58,7765,7769)"} true;
L6:

    // assume Identical($t18, Sub(simple_map::spec_get<address, u64>(select pool_u64::Pool.shares($t0), $t1), $t3)) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.spec.move:173:9+83
    assume {:print "$at(59,7278,7361)"} true;
    assume ($t18 == ($1_simple_map_spec_get'address_u64'($shares#$1_pool_u64_Pool($Dereference($t0)), $t1) - $t3));

    // assume Identical($t19, Sub(simple_map::spec_get<address, u64>(select pool_u64::Pool.shares($t0), $t1), $t3)) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.spec.move:181:9+83
    assume {:print "$at(59,7643,7726)"} true;
    assume ($t19 == ($1_simple_map_spec_get'address_u64'($shares#$1_pool_u64_Pool($Dereference($t0)), $t1) - $t3));

    // $t20 := pool_u64::deduct_shares($t0, $t1, $t3) on_abort goto L9 with $t8 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:189:9+54
    assume {:print "$at(58,7751,7805)"} true;
    call $t20,$t0 := $1_pool_u64_deduct_shares($t0, $t1, $t3);
    if ($abort_flag) {
        assume {:print "$at(58,7751,7805)"} true;
        $t8 := $abort_code;
        assume {:print "$track_abort(55,20):", $t8} $t8 == $t8;
        goto L9;
    }

    // destroy($t20) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:189:9+54

    // assume Identical($t21, simple_map::spec_contains_key<address, u64>(select pool_u64::Pool.shares($t0), $t2)) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.spec.move:74:9+73
    assume {:print "$at(59,2864,2937)"} true;
    assume ($t21 == $1_simple_map_spec_contains_key'address_u64'($shares#$1_pool_u64_Pool($Dereference($t0)), $t2));

    // assume Identical($t22, simple_map::spec_contains_key<address, u64>(select pool_u64::Pool.shares($t0), $t2)) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.spec.move:83:9+73
    assume {:print "$at(59,3186,3259)"} true;
    assume ($t22 == $1_simple_map_spec_contains_key'address_u64'($shares#$1_pool_u64_Pool($Dereference($t0)), $t2));

    // assume Identical($t23, simple_map::spec_get<address, u64>(select pool_u64::Pool.shares($t0), $t2)) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.spec.move:84:9+68
    assume {:print "$at(59,3268,3336)"} true;
    assume ($t23 == $1_simple_map_spec_get'address_u64'($shares#$1_pool_u64_Pool($Dereference($t0)), $t2));

    // assume Identical($t24, simple_map::spec_contains_key<address, u64>(select pool_u64::Pool.shares($t0), $t2)) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.spec.move:94:9+73
    assume {:print "$at(59,3636,3709)"} true;
    assume ($t24 == $1_simple_map_spec_contains_key'address_u64'($shares#$1_pool_u64_Pool($Dereference($t0)), $t2));

    // assume Identical($t25, simple_map::spec_get<address, u64>(select pool_u64::Pool.shares($t0), $t2)) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.spec.move:95:9+68
    assume {:print "$at(59,3718,3786)"} true;
    assume ($t25 == $1_simple_map_spec_get'address_u64'($shares#$1_pool_u64_Pool($Dereference($t0)), $t2));

    // $t26 := pool_u64::add_shares($t0, $t2, $t3) on_abort goto L9 with $t8 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:190:9+51
    assume {:print "$at(58,7815,7866)"} true;
    call $t26,$t0 := $1_pool_u64_add_shares($t0, $t2, $t3);
    if ($abort_flag) {
        assume {:print "$at(58,7815,7866)"} true;
        $t8 := $abort_code;
        assume {:print "$track_abort(55,20):", $t8} $t8 == $t8;
        goto L9;
    }

    // destroy($t26) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:190:9+51

    // trace_local[pool]($t0) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:190:60+1
    $temp_0'$1_pool_u64_Pool' := $Dereference($t0);
    assume {:print "$track_local(55,20,0):", $temp_0'$1_pool_u64_Pool'} $temp_0'$1_pool_u64_Pool' == $temp_0'$1_pool_u64_Pool';

    // pack_ref_deep($t0) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:190:60+1

    // label L8 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:191:5+1
    assume {:print "$at(58,7872,7873)"} true;
L8:

    // return () at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:191:5+1
    assume {:print "$at(58,7872,7873)"} true;
    $ret0 := $t0;
    return;

    // label L9 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:191:5+1
L9:

    // abort($t8) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:191:5+1
    assume {:print "$at(58,7872,7873)"} true;
    $abort_code := $t8;
    $abort_flag := true;
    return;

}

// fun pool_u64::update_total_coins [baseline] at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:121:5+120
procedure {:inline 1} $1_pool_u64_update_total_coins(_$t0: $Mutation ($1_pool_u64_Pool), _$t1: int) returns ($ret0: $Mutation ($1_pool_u64_Pool))
{
    // declare local variables
    var $t2: $Mutation (int);
    var $t0: $Mutation ($1_pool_u64_Pool);
    var $t1: int;
    var $temp_0'$1_pool_u64_Pool': $1_pool_u64_Pool;
    var $temp_0'u64': int;
    $t0 := _$t0;
    $t1 := _$t1;

    // bytecode translation starts here
    // trace_local[pool]($t0) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:121:5+1
    assume {:print "$at(58,4634,4635)"} true;
    $temp_0'$1_pool_u64_Pool' := $Dereference($t0);
    assume {:print "$track_local(55,21,0):", $temp_0'$1_pool_u64_Pool'} $temp_0'$1_pool_u64_Pool' == $temp_0'$1_pool_u64_Pool';

    // trace_local[new_total_coins]($t1) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:121:5+1
    assume {:print "$track_local(55,21,1):", $t1} $t1 == $t1;

    // $t2 := borrow_field<pool_u64::Pool>.total_coins($t0) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:122:9+16
    assume {:print "$at(58,4713,4729)"} true;
    $t2 := $ChildMutation($t0, 1, $total_coins#$1_pool_u64_Pool($Dereference($t0)));

    // write_ref($t2, $t1) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:122:9+34
    $t2 := $UpdateMutation($t2, $t1);

    // write_back[Reference($t0).total_coins (u64)]($t2) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:122:9+34
    $t0 := $UpdateMutation($t0, $Update'$1_pool_u64_Pool'_total_coins($Dereference($t0), $Dereference($t2)));

    // trace_local[pool]($t0) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:122:9+34
    $temp_0'$1_pool_u64_Pool' := $Dereference($t0);
    assume {:print "$track_local(55,21,0):", $temp_0'$1_pool_u64_Pool'} $temp_0'$1_pool_u64_Pool' == $temp_0'$1_pool_u64_Pool';

    // trace_local[pool]($t0) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:122:43+1
    $temp_0'$1_pool_u64_Pool' := $Dereference($t0);
    assume {:print "$track_local(55,21,0):", $temp_0'$1_pool_u64_Pool'} $temp_0'$1_pool_u64_Pool' == $temp_0'$1_pool_u64_Pool';

    // pack_ref_deep($t0) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:122:43+1

    // label L1 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:123:5+1
    assume {:print "$at(58,4753,4754)"} true;
L1:

    // return () at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.move:123:5+1
    assume {:print "$at(58,4753,4754)"} true;
    $ret0 := $t0;
    return;

}

// fun staking_contract::update_distribution_pool [verification] at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/staking_contract.move:692:5+5939
procedure {:timeLimit 2000} $1_staking_contract_update_distribution_pool$verify(_$t0: $Mutation ($1_pool_u64_Pool), _$t1: int, _$t2: int, _$t3: int) returns ($ret0: $Mutation ($1_pool_u64_Pool))
{
    // declare local variables
    var $t4: Vec (int);
    var $t5: int;
    var $t6: int;
    var $t7: int;
    var $t8: int;
    var $t9: int;
    var $t10: int;
    var $t11: int;
    var $t12: int;
    var $t13: int;
    var $t14: int;
    var $t15: Vec (int);
    var $t16: int;
    var $t17: int;
    var $t18: int;
    var $t19: $1_pool_u64_Pool;
    var $t20: int;
    var $t21: int;
    var $t22: bool;
    var $t23: $1_pool_u64_Pool;
    var $t24: Vec (int);
    var $t25: int;
    var $t26: int;
    var $t27: bool;
    var $t28: int;
    var $t29: bool;
    var $t30: $1_pool_u64_Pool;
    var $t31: int;
    var $t32: $1_pool_u64_Pool;
    var $t33: int;
    var $t34: $1_pool_u64_Pool;
    var $t35: int;
    var $t36: int;
    var $t37: int;
    var $t38: int;
    var $t39: int;
    var $t40: $1_pool_u64_Pool;
    var $t41: int;
    var $t42: int;
    var $t43: int;
    var $t44: int;
    var $t45: int;
    var $t0: $Mutation ($1_pool_u64_Pool);
    var $t1: int;
    var $t2: int;
    var $t3: int;
    var $temp_0'$1_pool_u64_Pool': $1_pool_u64_Pool;
    var $temp_0'address': int;
    var $temp_0'u64': int;
    var $temp_0'vec'address'': Vec (int);
    $t0 := _$t0;
    $t1 := _$t1;
    $t2 := _$t2;
    $t3 := _$t3;

    // verification entrypoint assumptions
    call $InitVerification();
    assume l#$Mutation($t0) == $Param(0);

    // bytecode translation starts here
    // assume And(WellFormed($t0), And(forall addr: TypeDomain<address>(): Eq<bool>(simple_map::spec_contains_key<address, u64>(select pool_u64::Pool.shares($t0), addr), vector::spec_contains<address>(select pool_u64::Pool.shareholders($t0), addr)), forall i: Range(0, Len<address>(select pool_u64::Pool.shareholders($t0))), j: Range(0, Len<address>(select pool_u64::Pool.shareholders($t0))): Implies(Eq<address>(Index(select pool_u64::Pool.shareholders($t0), i), Index(select pool_u64::Pool.shareholders($t0), j)), Eq<num>(i, j)))) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/staking_contract.move:692:5+1
    assume {:print "$at(2,33342,33343)"} true;
    assume ($IsValid'$1_pool_u64_Pool'($Dereference($t0)) && ((forall addr: int :: $IsValid'address'(addr) ==> ($IsEqual'bool'($1_simple_map_spec_contains_key'address_u64'($shares#$1_pool_u64_Pool($Dereference($t0)), addr), $1_vector_spec_contains'address'($shareholders#$1_pool_u64_Pool($Dereference($t0)), addr)))) && (var $range_0 := $Range(0, LenVec($shareholders#$1_pool_u64_Pool($Dereference($t0)))); (var $range_1 := $Range(0, LenVec($shareholders#$1_pool_u64_Pool($Dereference($t0)))); (forall $i_2: int, $i_3: int :: $InRange($range_0, $i_2) ==> $InRange($range_1, $i_3) ==> (var i := $i_2;
    (var j := $i_3;
    (($IsEqual'address'(ReadVec($shareholders#$1_pool_u64_Pool($Dereference($t0)), i), ReadVec($shareholders#$1_pool_u64_Pool($Dereference($t0)), j)) ==> $IsEqual'num'(i, j))))))))));

    // assume WellFormed($t1) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/staking_contract.move:692:5+1
    assume $IsValid'u64'($t1);

    // assume WellFormed($t2) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/staking_contract.move:692:5+1
    assume $IsValid'address'($t2);

    // assume WellFormed($t3) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/staking_contract.move:692:5+1
    assume $IsValid'u64'($t3);

    // trace_local[distribution_pool]($t0) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/staking_contract.move:692:5+1
    $temp_0'$1_pool_u64_Pool' := $Dereference($t0);
    assume {:print "$track_local(56,24,0):", $temp_0'$1_pool_u64_Pool'} $temp_0'$1_pool_u64_Pool' == $temp_0'$1_pool_u64_Pool';

    // trace_local[updated_total_coins]($t1) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/staking_contract.move:692:5+1
    assume {:print "$track_local(56,24,1):", $t1} $t1 == $t1;

    // trace_local[operator]($t2) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/staking_contract.move:692:5+1
    assume {:print "$track_local(56,24,2):", $t2} $t2 == $t2;

    // trace_local[commission_percentage]($t3) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/staking_contract.move:692:5+1
    assume {:print "$track_local(56,24,3):", $t3} $t3 == $t3;

    // $t19 := read_ref($t0) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/staking_contract.move:699:35+17
    assume {:print "$at(2,33632,33649)"} true;
    $t19 := $Dereference($t0);

    // $t20 := pool_u64::total_coins($t19) on_abort goto L10 with $t21 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/staking_contract.move:699:13+40
    call $t20 := $1_pool_u64_total_coins($t19);
    if ($abort_flag) {
        assume {:print "$at(2,33610,33650)"} true;
        $t21 := $abort_code;
        assume {:print "$track_abort(56,24):", $t21} $t21 == $t21;
        goto L10;
    }

    // $t22 := ==($t20, $t1) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/staking_contract.move:699:54+2
    $t22 := $IsEqual'u64'($t20, $t1);

    // if ($t22) goto L1 else goto L0 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/staking_contract.move:699:9+99
    if ($t22) { goto L1; } else { goto L0; }

    // label L1 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/staking_contract.move:700:13+6
    assume {:print "$at(2,33689,33695)"} true;
L1:

    // destroy($t0) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/staking_contract.move:700:13+6
    assume {:print "$at(2,33689,33695)"} true;

    // trace_local[distribution_pool]($t0) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/staking_contract.move:700:13+6
    $temp_0'$1_pool_u64_Pool' := $Dereference($t0);
    assume {:print "$track_local(56,24,0):", $temp_0'$1_pool_u64_Pool'} $temp_0'$1_pool_u64_Pool' == $temp_0'$1_pool_u64_Pool';

    // assert forall addr: TypeDomain<address>(): Eq<bool>(simple_map::spec_contains_key<address, u64>(select pool_u64::Pool.shares($t0), addr), vector::spec_contains<address>(select pool_u64::Pool.shareholders($t0), addr)) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.spec.move:16:9+135
    // data invariant at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.spec.move:16:9+135
    assume {:print "$at(59,538,673)"} true;
    assert {:msg "assert_failed(59,538,673): data invariant does not hold"}
      (forall addr: int :: $IsValid'address'(addr) ==> ($IsEqual'bool'($1_simple_map_spec_contains_key'address_u64'($shares#$1_pool_u64_Pool($Dereference($t0)), addr), $1_vector_spec_contains'address'($shareholders#$1_pool_u64_Pool($Dereference($t0)), addr))));

    // assert forall i: Range(0, Len<address>(select pool_u64::Pool.shareholders($t0))), j: Range(0, Len<address>(select pool_u64::Pool.shareholders($t0))): Implies(Eq<address>(Index(select pool_u64::Pool.shareholders($t0), i), Index(select pool_u64::Pool.shareholders($t0), j)), Eq<num>(i, j)) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.spec.move:20:9+129
    // data invariant at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.spec.move:20:9+129
    assume {:print "$at(59,738,867)"} true;
    assert {:msg "assert_failed(59,738,867): data invariant does not hold"}
      (var $range_0 := $Range(0, LenVec($shareholders#$1_pool_u64_Pool($Dereference($t0)))); (var $range_1 := $Range(0, LenVec($shareholders#$1_pool_u64_Pool($Dereference($t0)))); (forall $i_2: int, $i_3: int :: $InRange($range_0, $i_2) ==> $InRange($range_1, $i_3) ==> (var i := $i_2;
    (var j := $i_3;
    (($IsEqual'address'(ReadVec($shareholders#$1_pool_u64_Pool($Dereference($t0)), i), ReadVec($shareholders#$1_pool_u64_Pool($Dereference($t0)), j)) ==> $IsEqual'num'(i, j))))))));

    // goto L9 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/staking_contract.move:700:13+6
    assume {:print "$at(2,33689,33695)"} true;
    goto L9;

    // label L0 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/staking_contract.move:705:52+17
    assume {:print "$at(2,33933,33950)"} true;
L0:

    // $t23 := read_ref($t0) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/staking_contract.move:705:52+17
    assume {:print "$at(2,33933,33950)"} true;
    $t23 := $Dereference($t0);

    // $t24 := pool_u64::shareholders($t23) on_abort goto L10 with $t21 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/staking_contract.move:705:29+41
    call $t24 := $1_pool_u64_shareholders($t23);
    if ($abort_flag) {
        assume {:print "$at(2,33910,33951)"} true;
        $t21 := $abort_code;
        assume {:print "$track_abort(56,24):", $t21} $t21 == $t21;
        goto L10;
    }

    // trace_local[shareholders]($t24) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/staking_contract.move:705:13+12
    assume {:print "$track_local(56,24,15):", $t24} $t24 == $t24;

    // $t25 := vector::length<address>($t24) on_abort goto L10 with $t21 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/staking_contract.move:706:19+28
    assume {:print "$at(2,33971,33999)"} true;
    call $t25 := $1_vector_length'address'($t24);
    if ($abort_flag) {
        assume {:print "$at(2,33971,33999)"} true;
        $t21 := $abort_code;
        assume {:print "$track_abort(56,24):", $t21} $t21 == $t21;
        goto L10;
    }

    // trace_local[len]($t25) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/staking_contract.move:706:13+3
    assume {:print "$track_local(56,24,12):", $t25} $t25 == $t25;

    // $t26 := 0 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/staking_contract.move:707:17+1
    assume {:print "$at(2,34017,34018)"} true;
    $t26 := 0;
    assume $IsValid'u64'($t26);

    // trace_local[i]($t26) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/staking_contract.move:707:13+1
    assume {:print "$track_local(56,24,11):", $t26} $t26 == $t26;

    // label L7 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/staking_contract.move:709:13+70
    assume {:print "$at(2,34049,34119)"} true;
L7:

    // assert Le($t26, Len<address>($t24)) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/staking_contract.move:710:17+33
    assume {:print "$at(2,34072,34105)"} true;
    assert {:msg "assert_failed(2,34072,34105): base case of the loop invariant does not hold"}
      ($t26 <= LenVec($t24));

    // $t11 := havoc[val]() at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/staking_contract.move:710:17+33
    havoc $t11;

    // assume WellFormed($t11) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/staking_contract.move:710:17+33
    assume $IsValid'u64'($t11);

    // $t27 := havoc[val]() at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/staking_contract.move:710:17+33
    havoc $t27;

    // assume WellFormed($t27) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/staking_contract.move:710:17+33
    assume $IsValid'bool'($t27);

    // $t28 := havoc[val]() at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/staking_contract.move:710:17+33
    havoc $t28;

    // assume WellFormed($t28) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/staking_contract.move:710:17+33
    assume $IsValid'address'($t28);

    // $t29 := havoc[val]() at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/staking_contract.move:710:17+33
    havoc $t29;

    // assume WellFormed($t29) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/staking_contract.move:710:17+33
    assume $IsValid'bool'($t29);

    // $t30 := havoc[val]() at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/staking_contract.move:710:17+33
    havoc $t30;

    // assume And(WellFormed($t30), And(forall addr: TypeDomain<address>(): Eq<bool>(simple_map::spec_contains_key<address, u64>(select pool_u64::Pool.shares($t30), addr), vector::spec_contains<address>(select pool_u64::Pool.shareholders($t30), addr)), forall i: Range(0, Len<address>(select pool_u64::Pool.shareholders($t30))), j: Range(0, Len<address>(select pool_u64::Pool.shareholders($t30))): Implies(Eq<address>(Index(select pool_u64::Pool.shareholders($t30), i), Index(select pool_u64::Pool.shareholders($t30), j)), Eq<num>(i, j)))) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/staking_contract.move:710:17+33
    assume ($IsValid'$1_pool_u64_Pool'($t30) && ((forall addr: int :: $IsValid'address'(addr) ==> ($IsEqual'bool'($1_simple_map_spec_contains_key'address_u64'($shares#$1_pool_u64_Pool($t30), addr), $1_vector_spec_contains'address'($shareholders#$1_pool_u64_Pool($t30), addr)))) && (var $range_0 := $Range(0, LenVec($shareholders#$1_pool_u64_Pool($t30))); (var $range_1 := $Range(0, LenVec($shareholders#$1_pool_u64_Pool($t30))); (forall $i_2: int, $i_3: int :: $InRange($range_0, $i_2) ==> $InRange($range_1, $i_3) ==> (var i := $i_2;
    (var j := $i_3;
    (($IsEqual'address'(ReadVec($shareholders#$1_pool_u64_Pool($t30), i), ReadVec($shareholders#$1_pool_u64_Pool($t30), j)) ==> $IsEqual'num'(i, j))))))))));

    // $t31 := havoc[val]() at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/staking_contract.move:710:17+33
    havoc $t31;

    // assume WellFormed($t31) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/staking_contract.move:710:17+33
    assume $IsValid'u64'($t31);

    // $t32 := havoc[val]() at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/staking_contract.move:710:17+33
    havoc $t32;

    // assume And(WellFormed($t32), And(forall addr: TypeDomain<address>(): Eq<bool>(simple_map::spec_contains_key<address, u64>(select pool_u64::Pool.shares($t32), addr), vector::spec_contains<address>(select pool_u64::Pool.shareholders($t32), addr)), forall i: Range(0, Len<address>(select pool_u64::Pool.shareholders($t32))), j: Range(0, Len<address>(select pool_u64::Pool.shareholders($t32))): Implies(Eq<address>(Index(select pool_u64::Pool.shareholders($t32), i), Index(select pool_u64::Pool.shareholders($t32), j)), Eq<num>(i, j)))) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/staking_contract.move:710:17+33
    assume ($IsValid'$1_pool_u64_Pool'($t32) && ((forall addr: int :: $IsValid'address'(addr) ==> ($IsEqual'bool'($1_simple_map_spec_contains_key'address_u64'($shares#$1_pool_u64_Pool($t32), addr), $1_vector_spec_contains'address'($shareholders#$1_pool_u64_Pool($t32), addr)))) && (var $range_0 := $Range(0, LenVec($shareholders#$1_pool_u64_Pool($t32))); (var $range_1 := $Range(0, LenVec($shareholders#$1_pool_u64_Pool($t32))); (forall $i_2: int, $i_3: int :: $InRange($range_0, $i_2) ==> $InRange($range_1, $i_3) ==> (var i := $i_2;
    (var j := $i_3;
    (($IsEqual'address'(ReadVec($shareholders#$1_pool_u64_Pool($t32), i), ReadVec($shareholders#$1_pool_u64_Pool($t32), j)) ==> $IsEqual'num'(i, j))))))))));

    // $t33 := havoc[val]() at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/staking_contract.move:710:17+33
    havoc $t33;

    // assume WellFormed($t33) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/staking_contract.move:710:17+33
    assume $IsValid'u64'($t33);

    // $t34 := havoc[val]() at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/staking_contract.move:710:17+33
    havoc $t34;

    // assume And(WellFormed($t34), And(forall addr: TypeDomain<address>(): Eq<bool>(simple_map::spec_contains_key<address, u64>(select pool_u64::Pool.shares($t34), addr), vector::spec_contains<address>(select pool_u64::Pool.shareholders($t34), addr)), forall i: Range(0, Len<address>(select pool_u64::Pool.shareholders($t34))), j: Range(0, Len<address>(select pool_u64::Pool.shareholders($t34))): Implies(Eq<address>(Index(select pool_u64::Pool.shareholders($t34), i), Index(select pool_u64::Pool.shareholders($t34), j)), Eq<num>(i, j)))) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/staking_contract.move:710:17+33
    assume ($IsValid'$1_pool_u64_Pool'($t34) && ((forall addr: int :: $IsValid'address'(addr) ==> ($IsEqual'bool'($1_simple_map_spec_contains_key'address_u64'($shares#$1_pool_u64_Pool($t34), addr), $1_vector_spec_contains'address'($shareholders#$1_pool_u64_Pool($t34), addr)))) && (var $range_0 := $Range(0, LenVec($shareholders#$1_pool_u64_Pool($t34))); (var $range_1 := $Range(0, LenVec($shareholders#$1_pool_u64_Pool($t34))); (forall $i_2: int, $i_3: int :: $InRange($range_0, $i_2) ==> $InRange($range_1, $i_3) ==> (var i := $i_2;
    (var j := $i_3;
    (($IsEqual'address'(ReadVec($shareholders#$1_pool_u64_Pool($t34), i), ReadVec($shareholders#$1_pool_u64_Pool($t34), j)) ==> $IsEqual'num'(i, j))))))))));

    // $t35 := havoc[val]() at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/staking_contract.move:710:17+33
    havoc $t35;

    // assume WellFormed($t35) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/staking_contract.move:710:17+33
    assume $IsValid'u64'($t35);

    // $t36 := havoc[val]() at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/staking_contract.move:710:17+33
    havoc $t36;

    // assume WellFormed($t36) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/staking_contract.move:710:17+33
    assume $IsValid'u64'($t36);

    // $t37 := havoc[val]() at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/staking_contract.move:710:17+33
    havoc $t37;

    // assume WellFormed($t37) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/staking_contract.move:710:17+33
    assume $IsValid'u64'($t37);

    // $t38 := havoc[val]() at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/staking_contract.move:710:17+33
    havoc $t38;

    // assume WellFormed($t38) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/staking_contract.move:710:17+33
    assume $IsValid'u64'($t38);

    // $t39 := havoc[val]() at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/staking_contract.move:710:17+33
    havoc $t39;

    // assume WellFormed($t39) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/staking_contract.move:710:17+33
    assume $IsValid'u64'($t39);

    // $t40 := havoc[val]() at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/staking_contract.move:710:17+33
    havoc $t40;

    // assume And(WellFormed($t40), And(forall addr: TypeDomain<address>(): Eq<bool>(simple_map::spec_contains_key<address, u64>(select pool_u64::Pool.shares($t40), addr), vector::spec_contains<address>(select pool_u64::Pool.shareholders($t40), addr)), forall i: Range(0, Len<address>(select pool_u64::Pool.shareholders($t40))), j: Range(0, Len<address>(select pool_u64::Pool.shareholders($t40))): Implies(Eq<address>(Index(select pool_u64::Pool.shareholders($t40), i), Index(select pool_u64::Pool.shareholders($t40), j)), Eq<num>(i, j)))) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/staking_contract.move:710:17+33
    assume ($IsValid'$1_pool_u64_Pool'($t40) && ((forall addr: int :: $IsValid'address'(addr) ==> ($IsEqual'bool'($1_simple_map_spec_contains_key'address_u64'($shares#$1_pool_u64_Pool($t40), addr), $1_vector_spec_contains'address'($shareholders#$1_pool_u64_Pool($t40), addr)))) && (var $range_0 := $Range(0, LenVec($shareholders#$1_pool_u64_Pool($t40))); (var $range_1 := $Range(0, LenVec($shareholders#$1_pool_u64_Pool($t40))); (forall $i_2: int, $i_3: int :: $InRange($range_0, $i_2) ==> $InRange($range_1, $i_3) ==> (var i := $i_2;
    (var j := $i_3;
    (($IsEqual'address'(ReadVec($shareholders#$1_pool_u64_Pool($t40), i), ReadVec($shareholders#$1_pool_u64_Pool($t40), j)) ==> $IsEqual'num'(i, j))))))))));

    // $t41 := havoc[val]() at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/staking_contract.move:710:17+33
    havoc $t41;

    // assume WellFormed($t41) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/staking_contract.move:710:17+33
    assume $IsValid'u64'($t41);

    // $t42 := havoc[val]() at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/staking_contract.move:710:17+33
    havoc $t42;

    // assume WellFormed($t42) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/staking_contract.move:710:17+33
    assume $IsValid'u64'($t42);

    // $t43 := havoc[val]() at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/staking_contract.move:710:17+33
    havoc $t43;

    // assume WellFormed($t43) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/staking_contract.move:710:17+33
    assume $IsValid'u64'($t43);

    // $t0 := havoc[mut]() at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/staking_contract.move:710:17+33
    havoc $temp_0'$1_pool_u64_Pool';
    $t0 := $UpdateMutation($t0, $temp_0'$1_pool_u64_Pool');

    // assume And(WellFormed($t0), And(forall addr: TypeDomain<address>(): Eq<bool>(simple_map::spec_contains_key<address, u64>(select pool_u64::Pool.shares($t0), addr), vector::spec_contains<address>(select pool_u64::Pool.shareholders($t0), addr)), forall i: Range(0, Len<address>(select pool_u64::Pool.shareholders($t0))), j: Range(0, Len<address>(select pool_u64::Pool.shareholders($t0))): Implies(Eq<address>(Index(select pool_u64::Pool.shareholders($t0), i), Index(select pool_u64::Pool.shareholders($t0), j)), Eq<num>(i, j)))) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/staking_contract.move:710:17+33
    assume ($IsValid'$1_pool_u64_Pool'($Dereference($t0)) && ((forall addr: int :: $IsValid'address'(addr) ==> ($IsEqual'bool'($1_simple_map_spec_contains_key'address_u64'($shares#$1_pool_u64_Pool($Dereference($t0)), addr), $1_vector_spec_contains'address'($shareholders#$1_pool_u64_Pool($Dereference($t0)), addr)))) && (var $range_0 := $Range(0, LenVec($shareholders#$1_pool_u64_Pool($Dereference($t0)))); (var $range_1 := $Range(0, LenVec($shareholders#$1_pool_u64_Pool($Dereference($t0)))); (forall $i_2: int, $i_3: int :: $InRange($range_0, $i_2) ==> $InRange($range_1, $i_3) ==> (var i := $i_2;
    (var j := $i_3;
    (($IsEqual'address'(ReadVec($shareholders#$1_pool_u64_Pool($Dereference($t0)), i), ReadVec($shareholders#$1_pool_u64_Pool($Dereference($t0)), j)) ==> $IsEqual'num'(i, j))))))))));

    // trace_local[distribution_pool]($t0) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/staking_contract.move:710:17+33
    assume {:print "$info(): enter loop, variable(s) distribution_pool, i havocked and reassigned"} true;
    $temp_0'$1_pool_u64_Pool' := $Dereference($t0);
    assume {:print "$track_local(56,24,0):", $temp_0'$1_pool_u64_Pool'} $temp_0'$1_pool_u64_Pool' == $temp_0'$1_pool_u64_Pool';

    // trace_local[i]($t11) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/staking_contract.move:710:17+33
    assume {:print "$track_local(56,24,11):", $t11} $t11 == $t11;

    // assume Not(AbortFlag()) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/staking_contract.move:710:17+33
    assume {:print "$info(): loop invariant holds at current state"} true;
    assume !$abort_flag;

    // assume Le($t11, Len<address>($t24)) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/staking_contract.move:710:17+33
    assume ($t11 <= LenVec($t24));

    // $t27 := <($t11, $t25) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/staking_contract.move:712:16+1
    assume {:print "$at(2,34136,34137)"} true;
    call $t27 := $Lt($t11, $t25);

    // if ($t27) goto L3 else goto L2 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/staking_contract.move:708:9+5167
    assume {:print "$at(2,34028,39195)"} true;
    if ($t27) { goto L3; } else { goto L2; }

    // label L3 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/staking_contract.move:708:9+5167
L3:

    // label L4 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/staking_contract.move:714:47+12
    assume {:print "$at(2,34206,34218)"} true;
L4:

    // $t28 := vector::borrow<address>($t24, $t11) on_abort goto L10 with $t21 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/staking_contract.move:714:32+31
    assume {:print "$at(2,34191,34222)"} true;
    call $t28 := $1_vector_borrow'address'($t24, $t11);
    if ($abort_flag) {
        assume {:print "$at(2,34191,34222)"} true;
        $t21 := $abort_code;
        assume {:print "$track_abort(56,24):", $t21} $t21 == $t21;
        goto L10;
    }

    // trace_local[shareholder]($t28) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/staking_contract.move:714:17+11
    assume {:print "$track_local(56,24,14):", $t28} $t28 == $t28;

    // $t29 := !=($t28, $t2) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/staking_contract.move:715:29+2
    assume {:print "$at(2,34252,34254)"} true;
    $t29 := !$IsEqual'address'($t28, $t2);

    // if ($t29) goto L6 else goto L11 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/staking_contract.move:715:13+4924
    if ($t29) { goto L6; } else { goto L11; }

    // label L6 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/staking_contract.move:716:17+3816
    assume {:print "$at(2,34283,38099)"} true;
L6:

    // assume Implies(And(Gt(select pool_u64::Pool.total_coins($t0), 0), Gt(select pool_u64::Pool.total_shares($t0), 0)), Le(Div(Mul(pool_u64::spec_shares($t0, $t28), select pool_u64::Pool.total_coins($t0)), select pool_u64::Pool.total_shares($t0)), 18446744073709551615)) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/staking_contract.move:718:21+240
    assume {:print "$at(2,34348,34588)"} true;
    assume ((($total_coins#$1_pool_u64_Pool($Dereference($t0)) > 0) && ($total_shares#$1_pool_u64_Pool($Dereference($t0)) > 0)) ==> ((($1_pool_u64_spec_shares($Dereference($t0), $t28) * $total_coins#$1_pool_u64_Pool($Dereference($t0))) div $total_shares#$1_pool_u64_Pool($Dereference($t0))) <= 18446744073709551615));

    // assume Implies(And(Gt(select pool_u64::Pool.total_coins($t0), 0), Gt(select pool_u64::Pool.total_shares($t0), 0)), Le(Div(Mul(pool_u64::spec_shares($t0, $t28), $t1), select pool_u64::Pool.total_shares($t0)), 18446744073709551615)) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/staking_contract.move:721:21+230
    assume {:print "$at(2,34646,34876)"} true;
    assume ((($total_coins#$1_pool_u64_Pool($Dereference($t0)) > 0) && ($total_shares#$1_pool_u64_Pool($Dereference($t0)) > 0)) ==> ((($1_pool_u64_spec_shares($Dereference($t0), $t28) * $t1) div $total_shares#$1_pool_u64_Pool($Dereference($t0))) <= 18446744073709551615));

    // assume Ge(Sub(Div(Mul(pool_u64::spec_shares($t0, $t28), $t1), select pool_u64::Pool.total_shares($t0)), Div(Mul(pool_u64::spec_shares($t0, $t28), select pool_u64::Pool.total_coins($t0)), select pool_u64::Pool.total_shares($t0))), 0) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/staking_contract.move:724:21+270
    assume {:print "$at(2,34938,35208)"} true;
    assume (((($1_pool_u64_spec_shares($Dereference($t0), $t28) * $t1) div $total_shares#$1_pool_u64_Pool($Dereference($t0))) - (($1_pool_u64_spec_shares($Dereference($t0), $t28) * $total_coins#$1_pool_u64_Pool($Dereference($t0))) div $total_shares#$1_pool_u64_Pool($Dereference($t0)))) >= 0);

    // assume Le(Mul(Sub(Div(Mul(pool_u64::spec_shares($t0, $t28), $t1), select pool_u64::Pool.total_shares($t0)), Div(Mul(pool_u64::spec_shares($t0, $t28), select pool_u64::Pool.total_coins($t0)), select pool_u64::Pool.total_shares($t0))), $t3), 18446744073709551615) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/staking_contract.move:726:21+302
    assume {:print "$at(2,35229,35531)"} true;
    assume ((((($1_pool_u64_spec_shares($Dereference($t0), $t28) * $t1) div $total_shares#$1_pool_u64_Pool($Dereference($t0))) - (($1_pool_u64_spec_shares($Dereference($t0), $t28) * $total_coins#$1_pool_u64_Pool($Dereference($t0))) div $total_shares#$1_pool_u64_Pool($Dereference($t0)))) * $t3) <= 18446744073709551615);

    // assume Implies(And(Gt(select pool_u64::Pool.total_coins($t0), 0), Gt(select pool_u64::Pool.total_shares($t0), 0)), And(Neq<u64>($t1, 0), Le(Div(Mul(Div(Mul(Sub(Div(Mul(pool_u64::spec_shares($t0, $t28), $t1), select pool_u64::Pool.total_shares($t0)), Div(Mul(pool_u64::spec_shares($t0, $t28), select pool_u64::Pool.total_coins($t0)), select pool_u64::Pool.total_shares($t0))), $t3), 100), select pool_u64::Pool.total_shares($t0)), $t1), 18446744073709551615))) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/staking_contract.move:729:21+518
    assume {:print "$at(2,35594,36112)"} true;
    assume ((($total_coins#$1_pool_u64_Pool($Dereference($t0)) > 0) && ($total_shares#$1_pool_u64_Pool($Dereference($t0)) > 0)) ==> (!$IsEqual'u64'($t1, 0) && (((((((($1_pool_u64_spec_shares($Dereference($t0), $t28) * $t1) div $total_shares#$1_pool_u64_Pool($Dereference($t0))) - (($1_pool_u64_spec_shares($Dereference($t0), $t28) * $total_coins#$1_pool_u64_Pool($Dereference($t0))) div $total_shares#$1_pool_u64_Pool($Dereference($t0)))) * $t3) div 100) * $total_shares#$1_pool_u64_Pool($Dereference($t0))) div $t1) <= 18446744073709551615)));

    // assume pool_u64::spec_contains($t0, vector::$borrow<address>($t24, $t11)) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/staking_contract.move:734:21+83
    assume {:print "$at(2,36172,36255)"} true;
    assume $1_pool_u64_spec_contains($Dereference($t0), $1_vector_$borrow'address'($t24, $t11));

    // assume Ge(pool_u64::spec_shares($t0, $t28), Div(Mul(Div(Mul(Sub(Div(Mul(pool_u64::spec_shares($t0, $t28), $t1), select pool_u64::Pool.total_shares($t0)), Div(Mul(pool_u64::spec_shares($t0, $t28), select pool_u64::Pool.total_coins($t0)), select pool_u64::Pool.total_shares($t0))), $t3), 100), select pool_u64::Pool.total_shares($t0)), $t1)) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/staking_contract.move:735:21+461
    assume {:print "$at(2,36276,36737)"} true;
    assume ($1_pool_u64_spec_shares($Dereference($t0), $t28) >= ((((((($1_pool_u64_spec_shares($Dereference($t0), $t28) * $t1) div $total_shares#$1_pool_u64_Pool($Dereference($t0))) - (($1_pool_u64_spec_shares($Dereference($t0), $t28) * $total_coins#$1_pool_u64_Pool($Dereference($t0))) div $total_shares#$1_pool_u64_Pool($Dereference($t0)))) * $t3) div 100) * $total_shares#$1_pool_u64_Pool($Dereference($t0))) div $t1));

    // assume Implies(pool_u64::spec_contains($t0, $t2), Le(Add(simple_map::spec_get<address, u64>(select pool_u64::Pool.shares($t0), $t2), Div(Mul(Div(Mul(Sub(Div(Mul(pool_u64::spec_shares($t0, $t28), $t1), select pool_u64::Pool.total_shares($t0)), Div(Mul(pool_u64::spec_shares($t0, $t28), select pool_u64::Pool.total_coins($t0)), select pool_u64::Pool.total_shares($t0))), $t3), 100), select pool_u64::Pool.total_shares($t0)), $t1)), 18446744073709551615)) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/staking_contract.move:739:21+531
    assume {:print "$at(2,36758,37289)"} true;
    assume ($1_pool_u64_spec_contains($Dereference($t0), $t2) ==> (($1_simple_map_spec_get'address_u64'($shares#$1_pool_u64_Pool($Dereference($t0)), $t2) + ((((((($1_pool_u64_spec_shares($Dereference($t0), $t28) * $t1) div $total_shares#$1_pool_u64_Pool($Dereference($t0))) - (($1_pool_u64_spec_shares($Dereference($t0), $t28) * $total_coins#$1_pool_u64_Pool($Dereference($t0))) div $total_shares#$1_pool_u64_Pool($Dereference($t0)))) * $t3) div 100) * $total_shares#$1_pool_u64_Pool($Dereference($t0))) div $t1)) <= 18446744073709551615));

    // assume Implies(And(And(And(And(Not(pool_u64::spec_contains($t0, $t2)), Gt(select pool_u64::Pool.total_coins($t0), 0)), Gt(select pool_u64::Pool.total_shares($t0), 0)), Neq<u64>($t1, 0)), Gt(Div(Mul(Div(Mul(Sub(Div(Mul(pool_u64::spec_shares($t0, $t28), $t1), select pool_u64::Pool.total_shares($t0)), Div(Mul(pool_u64::spec_shares($t0, $t28), select pool_u64::Pool.total_coins($t0)), select pool_u64::Pool.total_shares($t0))), $t3), 100), select pool_u64::Pool.total_shares($t0)), $t1), 0)), Lt($t25, select pool_u64::Pool.shareholders_limit($t0))) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/staking_contract.move:743:21+639
    assume {:print "$at(2,37310,37949)"} true;
    assume (((((!$1_pool_u64_spec_contains($Dereference($t0), $t2) && ($total_coins#$1_pool_u64_Pool($Dereference($t0)) > 0)) && ($total_shares#$1_pool_u64_Pool($Dereference($t0)) > 0)) && !$IsEqual'u64'($t1, 0)) && (((((((($1_pool_u64_spec_shares($Dereference($t0), $t28) * $t1) div $total_shares#$1_pool_u64_Pool($Dereference($t0))) - (($1_pool_u64_spec_shares($Dereference($t0), $t28) * $total_coins#$1_pool_u64_Pool($Dereference($t0))) div $total_shares#$1_pool_u64_Pool($Dereference($t0)))) * $t3) div 100) * $total_shares#$1_pool_u64_Pool($Dereference($t0))) div $t1) > 0)) ==> ($t25 < $shareholders_limit#$1_pool_u64_Pool($Dereference($t0))));

    // $t30 := read_ref($t0) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/staking_contract.move:750:46+32
    assume {:print "$at(2,38146,38178)"} true;
    $t30 := $Dereference($t0);

    // $t31 := pool_u64::shares($t30, $t28) on_abort goto L10 with $t21 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/staking_contract.move:750:30+48
    call $t31 := $1_pool_u64_shares($t30, $t28);
    if ($abort_flag) {
        assume {:print "$at(2,38130,38178)"} true;
        $t21 := $abort_code;
        assume {:print "$track_abort(56,24):", $t21} $t21 == $t21;
        goto L10;
    }

    // trace_local[shares]($t31) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/staking_contract.move:750:21+6
    assume {:print "$track_local(56,24,16):", $t31} $t31 == $t31;

    // $t32 := read_ref($t0) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/staking_contract.move:751:55+32
    assume {:print "$at(2,38234,38266)"} true;
    $t32 := $Dereference($t0);

    // assume Identical($t44, pool_u64::spec_shares($t32, $t28)) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.spec.move:53:9+44
    assume {:print "$at(59,1730,1774)"} true;
    assume ($t44 == $1_pool_u64_spec_shares($t32, $t28));

    // assume Identical($t45, select pool_u64::Pool.total_coins($t32)) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.spec.move:54:9+35
    assume {:print "$at(59,1783,1818)"} true;
    assume ($t45 == $total_coins#$1_pool_u64_Pool($t32));

    // $t33 := pool_u64::balance($t32, $t28) on_abort goto L10 with $t21 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/staking_contract.move:751:38+49
    assume {:print "$at(2,38217,38266)"} true;
    call $t33 := $1_pool_u64_balance($t32, $t28);
    if ($abort_flag) {
        assume {:print "$at(2,38217,38266)"} true;
        $t21 := $abort_code;
        assume {:print "$track_abort(56,24):", $t21} $t21 == $t21;
        goto L10;
    }

    // trace_local[previous_worth]($t33) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/staking_contract.move:751:21+14
    assume {:print "$track_local(56,24,13):", $t33} $t33 == $t33;

    // $t34 := read_ref($t0) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/staking_contract.move:752:80+69
    assume {:print "$at(2,38347,38416)"} true;
    $t34 := $Dereference($t0);

    // $t35 := pool_u64::shares_to_amount_with_total_coins($t34, $t31, $t1) on_abort goto L10 with $t21 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/staking_contract.move:752:37+112
    call $t35 := $1_pool_u64_shares_to_amount_with_total_coins($t34, $t31, $t1);
    if ($abort_flag) {
        assume {:print "$at(2,38304,38416)"} true;
        $t21 := $abort_code;
        assume {:print "$track_abort(56,24):", $t21} $t21 == $t21;
        goto L10;
    }

    // $t36 := -($t35, $t33) on_abort goto L10 with $t21 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/staking_contract.move:754:56+1
    assume {:print "$at(2,38473,38474)"} true;
    call $t36 := $Sub($t35, $t33);
    if ($abort_flag) {
        assume {:print "$at(2,38473,38474)"} true;
        $t21 := $abort_code;
        assume {:print "$track_abort(56,24):", $t21} $t21 == $t21;
        goto L10;
    }

    // $t37 := *($t36, $t3) on_abort goto L10 with $t21 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/staking_contract.move:754:74+1
    call $t37 := $MulU64($t36, $t3);
    if ($abort_flag) {
        assume {:print "$at(2,38491,38492)"} true;
        $t21 := $abort_code;
        assume {:print "$track_abort(56,24):", $t21} $t21 == $t21;
        goto L10;
    }

    // $t38 := 100 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/staking_contract.move:754:100+3
    $t38 := 100;
    assume $IsValid'u64'($t38);

    // $t39 := /($t37, $t38) on_abort goto L10 with $t21 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/staking_contract.move:754:98+1
    call $t39 := $Div($t37, $t38);
    if ($abort_flag) {
        assume {:print "$at(2,38515,38516)"} true;
        $t21 := $abort_code;
        assume {:print "$track_abort(56,24):", $t21} $t21 == $t21;
        goto L10;
    }

    // trace_local[unpaid_commission]($t39) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/staking_contract.move:754:21+17
    assume {:print "$track_local(56,24,18):", $t39} $t39 == $t39;

    // $t40 := read_ref($t0) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/staking_contract.move:757:85+80
    assume {:print "$at(2,38780,38860)"} true;
    $t40 := $Dereference($t0);

    // $t41 := pool_u64::amount_to_shares_with_total_coins($t40, $t39, $t1) on_abort goto L10 with $t21 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/staking_contract.move:757:42+123
    call $t41 := $1_pool_u64_amount_to_shares_with_total_coins($t40, $t39, $t1);
    if ($abort_flag) {
        assume {:print "$at(2,38737,38860)"} true;
        $t21 := $abort_code;
        assume {:print "$track_abort(56,24):", $t21} $t21 == $t21;
        goto L10;
    }

    // trace_local[shares_to_transfer]($t41) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/staking_contract.move:757:21+18
    assume {:print "$track_local(56,24,17):", $t41} $t41 == $t41;

    // pool_u64::transfer_shares($t0, $t28, $t2, $t41) on_abort goto L10 with $t21 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/staking_contract.move:762:17+87
    assume {:print "$at(2,39058,39145)"} true;
    call $t0 := $1_pool_u64_transfer_shares($t0, $t28, $t2, $t41);
    if ($abort_flag) {
        assume {:print "$at(2,39058,39145)"} true;
        $t21 := $abort_code;
        assume {:print "$track_abort(56,24):", $t21} $t21 == $t21;
        goto L10;
    }

    // label L5 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/staking_contract.move:765:17+1
    assume {:print "$at(2,39179,39180)"} true;
L5:

    // $t42 := 1 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/staking_contract.move:765:21+1
    assume {:print "$at(2,39183,39184)"} true;
    $t42 := 1;
    assume $IsValid'u64'($t42);

    // $t43 := +($t11, $t42) on_abort goto L10 with $t21 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/staking_contract.move:765:19+1
    call $t43 := $AddU64($t11, $t42);
    if ($abort_flag) {
        assume {:print "$at(2,39181,39182)"} true;
        $t21 := $abort_code;
        assume {:print "$track_abort(56,24):", $t21} $t21 == $t21;
        goto L10;
    }

    // trace_local[i]($t43) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/staking_contract.move:765:13+1
    assume {:print "$track_local(56,24,11):", $t43} $t43 == $t43;

    // goto L8 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/staking_contract.move:765:22+1
    goto L8;

    // label L2 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/staking_contract.move:768:9+68
    assume {:print "$at(2,39206,39274)"} true;
L2:

    // pool_u64::update_total_coins($t0, $t1) on_abort goto L10 with $t21 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/staking_contract.move:768:9+68
    assume {:print "$at(2,39206,39274)"} true;
    call $t0 := $1_pool_u64_update_total_coins($t0, $t1);
    if ($abort_flag) {
        assume {:print "$at(2,39206,39274)"} true;
        $t21 := $abort_code;
        assume {:print "$track_abort(56,24):", $t21} $t21 == $t21;
        goto L10;
    }

    // trace_local[distribution_pool]($t0) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/staking_contract.move:768:77+1
    $temp_0'$1_pool_u64_Pool' := $Dereference($t0);
    assume {:print "$track_local(56,24,0):", $temp_0'$1_pool_u64_Pool'} $temp_0'$1_pool_u64_Pool' == $temp_0'$1_pool_u64_Pool';

    // assert forall addr: TypeDomain<address>(): Eq<bool>(simple_map::spec_contains_key<address, u64>(select pool_u64::Pool.shares($t0), addr), vector::spec_contains<address>(select pool_u64::Pool.shareholders($t0), addr)) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.spec.move:16:9+135
    // data invariant at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.spec.move:16:9+135
    assume {:print "$at(59,538,673)"} true;
    assert {:msg "assert_failed(59,538,673): data invariant does not hold"}
      (forall addr: int :: $IsValid'address'(addr) ==> ($IsEqual'bool'($1_simple_map_spec_contains_key'address_u64'($shares#$1_pool_u64_Pool($Dereference($t0)), addr), $1_vector_spec_contains'address'($shareholders#$1_pool_u64_Pool($Dereference($t0)), addr))));

    // assert forall i: Range(0, Len<address>(select pool_u64::Pool.shareholders($t0))), j: Range(0, Len<address>(select pool_u64::Pool.shareholders($t0))): Implies(Eq<address>(Index(select pool_u64::Pool.shareholders($t0), i), Index(select pool_u64::Pool.shareholders($t0), j)), Eq<num>(i, j)) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.spec.move:20:9+129
    // data invariant at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/pool_u64.spec.move:20:9+129
    assume {:print "$at(59,738,867)"} true;
    assert {:msg "assert_failed(59,738,867): data invariant does not hold"}
      (var $range_0 := $Range(0, LenVec($shareholders#$1_pool_u64_Pool($Dereference($t0)))); (var $range_1 := $Range(0, LenVec($shareholders#$1_pool_u64_Pool($Dereference($t0)))); (forall $i_2: int, $i_3: int :: $InRange($range_0, $i_2) ==> $InRange($range_1, $i_3) ==> (var i := $i_2;
    (var j := $i_3;
    (($IsEqual'address'(ReadVec($shareholders#$1_pool_u64_Pool($Dereference($t0)), i), ReadVec($shareholders#$1_pool_u64_Pool($Dereference($t0)), j)) ==> $IsEqual'num'(i, j))))))));

    // goto L9 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/staking_contract.move:768:77+1
    assume {:print "$at(2,39274,39275)"} true;
    goto L9;

    // label L8 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/staking_contract.move:768:9+68
    // Loop invariant checking block for the loop started with header: L7
L8:

    // assert Le($t43, Len<address>($t24)) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/staking_contract.move:710:17+33
    assume {:print "$at(2,34072,34105)"} true;
    assert {:msg "assert_failed(2,34072,34105): induction case of the loop invariant does not hold"}
      ($t43 <= LenVec($t24));

    // stop() at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/staking_contract.move:710:17+33
    assume false;
    return;

    // label L9 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/staking_contract.move:769:5+1
    assume {:print "$at(2,39280,39281)"} true;
L9:

    // assert Not(false) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/staking_contract.move:769:5+1
    assume {:print "$at(2,39280,39281)"} true;
    assert {:msg "assert_failed(2,39280,39281): function does not abort under this condition"}
      !false;

    // return () at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/staking_contract.move:769:5+1
    $ret0 := $t0;
    return;

    // label L10 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/staking_contract.move:769:5+1
L10:

    // assert false at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/staking_contract.spec.move:405:5+306
    assume {:print "$at(3,22480,22786)"} true;
    assert {:msg "assert_failed(3,22480,22786): abort not covered by any of the `aborts_if` clauses"}
      false;

    // abort($t21) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/staking_contract.spec.move:405:5+306
    $abort_code := $t21;
    $abort_flag := true;
    return;

    // label L11 at <internal>:1:1+10
    assume {:print "$at(1,0,10)"} true;
L11:

    // destroy($t0) at <internal>:1:1+10
    assume {:print "$at(1,0,10)"} true;

    // goto L5 at <internal>:1:1+10
    goto L5;

}
