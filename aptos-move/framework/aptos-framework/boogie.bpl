
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
// Native Vector implementation for element type `#0`

// Not inlined. It appears faster this way.
function $IsEqual'vec'#0''(v1: Vec (#0), v2: Vec (#0)): bool {
    LenVec(v1) == LenVec(v2) &&
    (forall i: int:: InRangeVec(v1, i) ==> $IsEqual'#0'(ReadVec(v1, i), ReadVec(v2, i)))
}

// Not inlined.
function $IsPrefix'vec'#0''(v: Vec (#0), prefix: Vec (#0)): bool {
    LenVec(v) >= LenVec(prefix) &&
    (forall i: int:: InRangeVec(prefix, i) ==> $IsEqual'#0'(ReadVec(v, i), ReadVec(prefix, i)))
}

// Not inlined.
function $IsSuffix'vec'#0''(v: Vec (#0), suffix: Vec (#0)): bool {
    LenVec(v) >= LenVec(suffix) &&
    (forall i: int:: InRangeVec(suffix, i) ==> $IsEqual'#0'(ReadVec(v, LenVec(v) - LenVec(suffix) + i), ReadVec(suffix, i)))
}

// Not inlined.
function $IsValid'vec'#0''(v: Vec (#0)): bool {
    $IsValid'u64'(LenVec(v)) &&
    (forall i: int:: InRangeVec(v, i) ==> $IsValid'#0'(ReadVec(v, i)))
}


function {:inline} $ContainsVec'#0'(v: Vec (#0), e: #0): bool {
    (exists i: int :: $IsValid'u64'(i) && InRangeVec(v, i) && $IsEqual'#0'(ReadVec(v, i), e))
}

function $IndexOfVec'#0'(v: Vec (#0), e: #0): int;
axiom (forall v: Vec (#0), e: #0:: {$IndexOfVec'#0'(v, e)}
    (var i := $IndexOfVec'#0'(v, e);
     if (!$ContainsVec'#0'(v, e)) then i == -1
     else $IsValid'u64'(i) && InRangeVec(v, i) && $IsEqual'#0'(ReadVec(v, i), e) &&
        (forall j: int :: $IsValid'u64'(j) && j >= 0 && j < i ==> !$IsEqual'#0'(ReadVec(v, j), e))));


function {:inline} $RangeVec'#0'(v: Vec (#0)): $Range {
    $Range(0, LenVec(v))
}


function {:inline} $EmptyVec'#0'(): Vec (#0) {
    EmptyVec()
}

procedure {:inline 1} $1_vector_empty'#0'() returns (v: Vec (#0)) {
    v := EmptyVec();
}

function {:inline} $1_vector_$empty'#0'(): Vec (#0) {
    EmptyVec()
}

procedure {:inline 1} $1_vector_is_empty'#0'(v: Vec (#0)) returns (b: bool) {
    b := IsEmptyVec(v);
}

procedure {:inline 1} $1_vector_push_back'#0'(m: $Mutation (Vec (#0)), val: #0) returns (m': $Mutation (Vec (#0))) {
    m' := $UpdateMutation(m, ExtendVec($Dereference(m), val));
}

function {:inline} $1_vector_$push_back'#0'(v: Vec (#0), val: #0): Vec (#0) {
    ExtendVec(v, val)
}

procedure {:inline 1} $1_vector_pop_back'#0'(m: $Mutation (Vec (#0))) returns (e: #0, m': $Mutation (Vec (#0))) {
    var v: Vec (#0);
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

procedure {:inline 1} $1_vector_append'#0'(m: $Mutation (Vec (#0)), other: Vec (#0)) returns (m': $Mutation (Vec (#0))) {
    m' := $UpdateMutation(m, ConcatVec($Dereference(m), other));
}

procedure {:inline 1} $1_vector_reverse'#0'(m: $Mutation (Vec (#0))) returns (m': $Mutation (Vec (#0))) {
    m' := $UpdateMutation(m, ReverseVec($Dereference(m)));
}

procedure {:inline 1} $1_vector_reverse_append'#0'(m: $Mutation (Vec (#0)), other: Vec (#0)) returns (m': $Mutation (Vec (#0))) {
    m' := $UpdateMutation(m, ConcatVec($Dereference(m), ReverseVec(other)));
}

procedure {:inline 1} $1_vector_trim_reverse'#0'(m: $Mutation (Vec (#0)), new_len: int) returns (v: (Vec (#0)), m': $Mutation (Vec (#0))) {
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

procedure {:inline 1} $1_vector_trim'#0'(m: $Mutation (Vec (#0)), new_len: int) returns (v: (Vec (#0)), m': $Mutation (Vec (#0))) {
    var len: int;
    v := $Dereference(m);
    if (LenVec(v) < new_len) {
        call $ExecFailureAbort();
        return;
    }
    v := SliceVec(v, new_len, LenVec(v));
    m' := $UpdateMutation(m, SliceVec($Dereference(m), 0, new_len));
}

procedure {:inline 1} $1_vector_reverse_slice'#0'(m: $Mutation (Vec (#0)), left: int, right: int) returns (m': $Mutation (Vec (#0))) {
    var left_vec: Vec (#0);
    var mid_vec: Vec (#0);
    var right_vec: Vec (#0);
    var v: Vec (#0);
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

procedure {:inline 1} $1_vector_rotate'#0'(m: $Mutation (Vec (#0)), rot: int) returns (n: int, m': $Mutation (Vec (#0))) {
    var v: Vec (#0);
    var len: int;
    var left_vec: Vec (#0);
    var right_vec: Vec (#0);
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

procedure {:inline 1} $1_vector_rotate_slice'#0'(m: $Mutation (Vec (#0)), left: int, rot: int, right: int) returns (n: int, m': $Mutation (Vec (#0))) {
    var left_vec: Vec (#0);
    var mid_vec: Vec (#0);
    var right_vec: Vec (#0);
    var mid_left_vec: Vec (#0);
    var mid_right_vec: Vec (#0);
    var v: Vec (#0);
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

procedure {:inline 1} $1_vector_insert'#0'(m: $Mutation (Vec (#0)), i: int, e: #0) returns (m': $Mutation (Vec (#0))) {
    var left_vec: Vec (#0);
    var right_vec: Vec (#0);
    var v: Vec (#0);
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

procedure {:inline 1} $1_vector_length'#0'(v: Vec (#0)) returns (l: int) {
    l := LenVec(v);
}

function {:inline} $1_vector_$length'#0'(v: Vec (#0)): int {
    LenVec(v)
}

procedure {:inline 1} $1_vector_borrow'#0'(v: Vec (#0), i: int) returns (dst: #0) {
    if (!InRangeVec(v, i)) {
        call $ExecFailureAbort();
        return;
    }
    dst := ReadVec(v, i);
}

function {:inline} $1_vector_$borrow'#0'(v: Vec (#0), i: int): #0 {
    ReadVec(v, i)
}

procedure {:inline 1} $1_vector_borrow_mut'#0'(m: $Mutation (Vec (#0)), index: int)
returns (dst: $Mutation (#0), m': $Mutation (Vec (#0)))
{
    var v: Vec (#0);
    v := $Dereference(m);
    if (!InRangeVec(v, index)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Mutation(l#$Mutation(m), ExtendVec(p#$Mutation(m), index), ReadVec(v, index));
    m' := m;
}

function {:inline} $1_vector_$borrow_mut'#0'(v: Vec (#0), i: int): #0 {
    ReadVec(v, i)
}

procedure {:inline 1} $1_vector_destroy_empty'#0'(v: Vec (#0)) {
    if (!IsEmptyVec(v)) {
      call $ExecFailureAbort();
    }
}

procedure {:inline 1} $1_vector_swap'#0'(m: $Mutation (Vec (#0)), i: int, j: int) returns (m': $Mutation (Vec (#0)))
{
    var v: Vec (#0);
    v := $Dereference(m);
    if (!InRangeVec(v, i) || !InRangeVec(v, j)) {
        call $ExecFailureAbort();
        return;
    }
    m' := $UpdateMutation(m, SwapVec(v, i, j));
}

function {:inline} $1_vector_$swap'#0'(v: Vec (#0), i: int, j: int): Vec (#0) {
    SwapVec(v, i, j)
}

procedure {:inline 1} $1_vector_remove'#0'(m: $Mutation (Vec (#0)), i: int) returns (e: #0, m': $Mutation (Vec (#0)))
{
    var v: Vec (#0);

    v := $Dereference(m);

    if (!InRangeVec(v, i)) {
        call $ExecFailureAbort();
        return;
    }
    e := ReadVec(v, i);
    m' := $UpdateMutation(m, RemoveAtVec(v, i));
}

procedure {:inline 1} $1_vector_swap_remove'#0'(m: $Mutation (Vec (#0)), i: int) returns (e: #0, m': $Mutation (Vec (#0)))
{
    var len: int;
    var v: Vec (#0);

    v := $Dereference(m);
    len := LenVec(v);
    if (!InRangeVec(v, i)) {
        call $ExecFailureAbort();
        return;
    }
    e := ReadVec(v, i);
    m' := $UpdateMutation(m, RemoveVec(SwapVec(v, i, len-1)));
}

procedure {:inline 1} $1_vector_contains'#0'(v: Vec (#0), e: #0) returns (res: bool)  {
    res := $ContainsVec'#0'(v, e);
}

procedure {:inline 1}
$1_vector_index_of'#0'(v: Vec (#0), e: #0) returns (res1: bool, res2: int) {
    res2 := $IndexOfVec'#0'(v, e);
    if (res2 >= 0) {
        res1 := true;
    } else {
        res1 := false;
        res2 := 0;
    }
}


// ----------------------------------------------------------------------------------
// Native Vector implementation for element type `$1_governance_proposal_GovernanceProposal`

// Not inlined. It appears faster this way.
function $IsEqual'vec'$1_governance_proposal_GovernanceProposal''(v1: Vec ($1_governance_proposal_GovernanceProposal), v2: Vec ($1_governance_proposal_GovernanceProposal)): bool {
    LenVec(v1) == LenVec(v2) &&
    (forall i: int:: InRangeVec(v1, i) ==> $IsEqual'$1_governance_proposal_GovernanceProposal'(ReadVec(v1, i), ReadVec(v2, i)))
}

// Not inlined.
function $IsPrefix'vec'$1_governance_proposal_GovernanceProposal''(v: Vec ($1_governance_proposal_GovernanceProposal), prefix: Vec ($1_governance_proposal_GovernanceProposal)): bool {
    LenVec(v) >= LenVec(prefix) &&
    (forall i: int:: InRangeVec(prefix, i) ==> $IsEqual'$1_governance_proposal_GovernanceProposal'(ReadVec(v, i), ReadVec(prefix, i)))
}

// Not inlined.
function $IsSuffix'vec'$1_governance_proposal_GovernanceProposal''(v: Vec ($1_governance_proposal_GovernanceProposal), suffix: Vec ($1_governance_proposal_GovernanceProposal)): bool {
    LenVec(v) >= LenVec(suffix) &&
    (forall i: int:: InRangeVec(suffix, i) ==> $IsEqual'$1_governance_proposal_GovernanceProposal'(ReadVec(v, LenVec(v) - LenVec(suffix) + i), ReadVec(suffix, i)))
}

// Not inlined.
function $IsValid'vec'$1_governance_proposal_GovernanceProposal''(v: Vec ($1_governance_proposal_GovernanceProposal)): bool {
    $IsValid'u64'(LenVec(v)) &&
    (forall i: int:: InRangeVec(v, i) ==> $IsValid'$1_governance_proposal_GovernanceProposal'(ReadVec(v, i)))
}


function {:inline} $ContainsVec'$1_governance_proposal_GovernanceProposal'(v: Vec ($1_governance_proposal_GovernanceProposal), e: $1_governance_proposal_GovernanceProposal): bool {
    (exists i: int :: $IsValid'u64'(i) && InRangeVec(v, i) && $IsEqual'$1_governance_proposal_GovernanceProposal'(ReadVec(v, i), e))
}

function $IndexOfVec'$1_governance_proposal_GovernanceProposal'(v: Vec ($1_governance_proposal_GovernanceProposal), e: $1_governance_proposal_GovernanceProposal): int;
axiom (forall v: Vec ($1_governance_proposal_GovernanceProposal), e: $1_governance_proposal_GovernanceProposal:: {$IndexOfVec'$1_governance_proposal_GovernanceProposal'(v, e)}
    (var i := $IndexOfVec'$1_governance_proposal_GovernanceProposal'(v, e);
     if (!$ContainsVec'$1_governance_proposal_GovernanceProposal'(v, e)) then i == -1
     else $IsValid'u64'(i) && InRangeVec(v, i) && $IsEqual'$1_governance_proposal_GovernanceProposal'(ReadVec(v, i), e) &&
        (forall j: int :: $IsValid'u64'(j) && j >= 0 && j < i ==> !$IsEqual'$1_governance_proposal_GovernanceProposal'(ReadVec(v, j), e))));


function {:inline} $RangeVec'$1_governance_proposal_GovernanceProposal'(v: Vec ($1_governance_proposal_GovernanceProposal)): $Range {
    $Range(0, LenVec(v))
}


function {:inline} $EmptyVec'$1_governance_proposal_GovernanceProposal'(): Vec ($1_governance_proposal_GovernanceProposal) {
    EmptyVec()
}

procedure {:inline 1} $1_vector_empty'$1_governance_proposal_GovernanceProposal'() returns (v: Vec ($1_governance_proposal_GovernanceProposal)) {
    v := EmptyVec();
}

function {:inline} $1_vector_$empty'$1_governance_proposal_GovernanceProposal'(): Vec ($1_governance_proposal_GovernanceProposal) {
    EmptyVec()
}

procedure {:inline 1} $1_vector_is_empty'$1_governance_proposal_GovernanceProposal'(v: Vec ($1_governance_proposal_GovernanceProposal)) returns (b: bool) {
    b := IsEmptyVec(v);
}

procedure {:inline 1} $1_vector_push_back'$1_governance_proposal_GovernanceProposal'(m: $Mutation (Vec ($1_governance_proposal_GovernanceProposal)), val: $1_governance_proposal_GovernanceProposal) returns (m': $Mutation (Vec ($1_governance_proposal_GovernanceProposal))) {
    m' := $UpdateMutation(m, ExtendVec($Dereference(m), val));
}

function {:inline} $1_vector_$push_back'$1_governance_proposal_GovernanceProposal'(v: Vec ($1_governance_proposal_GovernanceProposal), val: $1_governance_proposal_GovernanceProposal): Vec ($1_governance_proposal_GovernanceProposal) {
    ExtendVec(v, val)
}

procedure {:inline 1} $1_vector_pop_back'$1_governance_proposal_GovernanceProposal'(m: $Mutation (Vec ($1_governance_proposal_GovernanceProposal))) returns (e: $1_governance_proposal_GovernanceProposal, m': $Mutation (Vec ($1_governance_proposal_GovernanceProposal))) {
    var v: Vec ($1_governance_proposal_GovernanceProposal);
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

procedure {:inline 1} $1_vector_append'$1_governance_proposal_GovernanceProposal'(m: $Mutation (Vec ($1_governance_proposal_GovernanceProposal)), other: Vec ($1_governance_proposal_GovernanceProposal)) returns (m': $Mutation (Vec ($1_governance_proposal_GovernanceProposal))) {
    m' := $UpdateMutation(m, ConcatVec($Dereference(m), other));
}

procedure {:inline 1} $1_vector_reverse'$1_governance_proposal_GovernanceProposal'(m: $Mutation (Vec ($1_governance_proposal_GovernanceProposal))) returns (m': $Mutation (Vec ($1_governance_proposal_GovernanceProposal))) {
    m' := $UpdateMutation(m, ReverseVec($Dereference(m)));
}

procedure {:inline 1} $1_vector_reverse_append'$1_governance_proposal_GovernanceProposal'(m: $Mutation (Vec ($1_governance_proposal_GovernanceProposal)), other: Vec ($1_governance_proposal_GovernanceProposal)) returns (m': $Mutation (Vec ($1_governance_proposal_GovernanceProposal))) {
    m' := $UpdateMutation(m, ConcatVec($Dereference(m), ReverseVec(other)));
}

procedure {:inline 1} $1_vector_trim_reverse'$1_governance_proposal_GovernanceProposal'(m: $Mutation (Vec ($1_governance_proposal_GovernanceProposal)), new_len: int) returns (v: (Vec ($1_governance_proposal_GovernanceProposal)), m': $Mutation (Vec ($1_governance_proposal_GovernanceProposal))) {
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

procedure {:inline 1} $1_vector_trim'$1_governance_proposal_GovernanceProposal'(m: $Mutation (Vec ($1_governance_proposal_GovernanceProposal)), new_len: int) returns (v: (Vec ($1_governance_proposal_GovernanceProposal)), m': $Mutation (Vec ($1_governance_proposal_GovernanceProposal))) {
    var len: int;
    v := $Dereference(m);
    if (LenVec(v) < new_len) {
        call $ExecFailureAbort();
        return;
    }
    v := SliceVec(v, new_len, LenVec(v));
    m' := $UpdateMutation(m, SliceVec($Dereference(m), 0, new_len));
}

procedure {:inline 1} $1_vector_reverse_slice'$1_governance_proposal_GovernanceProposal'(m: $Mutation (Vec ($1_governance_proposal_GovernanceProposal)), left: int, right: int) returns (m': $Mutation (Vec ($1_governance_proposal_GovernanceProposal))) {
    var left_vec: Vec ($1_governance_proposal_GovernanceProposal);
    var mid_vec: Vec ($1_governance_proposal_GovernanceProposal);
    var right_vec: Vec ($1_governance_proposal_GovernanceProposal);
    var v: Vec ($1_governance_proposal_GovernanceProposal);
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

procedure {:inline 1} $1_vector_rotate'$1_governance_proposal_GovernanceProposal'(m: $Mutation (Vec ($1_governance_proposal_GovernanceProposal)), rot: int) returns (n: int, m': $Mutation (Vec ($1_governance_proposal_GovernanceProposal))) {
    var v: Vec ($1_governance_proposal_GovernanceProposal);
    var len: int;
    var left_vec: Vec ($1_governance_proposal_GovernanceProposal);
    var right_vec: Vec ($1_governance_proposal_GovernanceProposal);
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

procedure {:inline 1} $1_vector_rotate_slice'$1_governance_proposal_GovernanceProposal'(m: $Mutation (Vec ($1_governance_proposal_GovernanceProposal)), left: int, rot: int, right: int) returns (n: int, m': $Mutation (Vec ($1_governance_proposal_GovernanceProposal))) {
    var left_vec: Vec ($1_governance_proposal_GovernanceProposal);
    var mid_vec: Vec ($1_governance_proposal_GovernanceProposal);
    var right_vec: Vec ($1_governance_proposal_GovernanceProposal);
    var mid_left_vec: Vec ($1_governance_proposal_GovernanceProposal);
    var mid_right_vec: Vec ($1_governance_proposal_GovernanceProposal);
    var v: Vec ($1_governance_proposal_GovernanceProposal);
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

procedure {:inline 1} $1_vector_insert'$1_governance_proposal_GovernanceProposal'(m: $Mutation (Vec ($1_governance_proposal_GovernanceProposal)), i: int, e: $1_governance_proposal_GovernanceProposal) returns (m': $Mutation (Vec ($1_governance_proposal_GovernanceProposal))) {
    var left_vec: Vec ($1_governance_proposal_GovernanceProposal);
    var right_vec: Vec ($1_governance_proposal_GovernanceProposal);
    var v: Vec ($1_governance_proposal_GovernanceProposal);
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

procedure {:inline 1} $1_vector_length'$1_governance_proposal_GovernanceProposal'(v: Vec ($1_governance_proposal_GovernanceProposal)) returns (l: int) {
    l := LenVec(v);
}

function {:inline} $1_vector_$length'$1_governance_proposal_GovernanceProposal'(v: Vec ($1_governance_proposal_GovernanceProposal)): int {
    LenVec(v)
}

procedure {:inline 1} $1_vector_borrow'$1_governance_proposal_GovernanceProposal'(v: Vec ($1_governance_proposal_GovernanceProposal), i: int) returns (dst: $1_governance_proposal_GovernanceProposal) {
    if (!InRangeVec(v, i)) {
        call $ExecFailureAbort();
        return;
    }
    dst := ReadVec(v, i);
}

function {:inline} $1_vector_$borrow'$1_governance_proposal_GovernanceProposal'(v: Vec ($1_governance_proposal_GovernanceProposal), i: int): $1_governance_proposal_GovernanceProposal {
    ReadVec(v, i)
}

procedure {:inline 1} $1_vector_borrow_mut'$1_governance_proposal_GovernanceProposal'(m: $Mutation (Vec ($1_governance_proposal_GovernanceProposal)), index: int)
returns (dst: $Mutation ($1_governance_proposal_GovernanceProposal), m': $Mutation (Vec ($1_governance_proposal_GovernanceProposal)))
{
    var v: Vec ($1_governance_proposal_GovernanceProposal);
    v := $Dereference(m);
    if (!InRangeVec(v, index)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Mutation(l#$Mutation(m), ExtendVec(p#$Mutation(m), index), ReadVec(v, index));
    m' := m;
}

function {:inline} $1_vector_$borrow_mut'$1_governance_proposal_GovernanceProposal'(v: Vec ($1_governance_proposal_GovernanceProposal), i: int): $1_governance_proposal_GovernanceProposal {
    ReadVec(v, i)
}

procedure {:inline 1} $1_vector_destroy_empty'$1_governance_proposal_GovernanceProposal'(v: Vec ($1_governance_proposal_GovernanceProposal)) {
    if (!IsEmptyVec(v)) {
      call $ExecFailureAbort();
    }
}

procedure {:inline 1} $1_vector_swap'$1_governance_proposal_GovernanceProposal'(m: $Mutation (Vec ($1_governance_proposal_GovernanceProposal)), i: int, j: int) returns (m': $Mutation (Vec ($1_governance_proposal_GovernanceProposal)))
{
    var v: Vec ($1_governance_proposal_GovernanceProposal);
    v := $Dereference(m);
    if (!InRangeVec(v, i) || !InRangeVec(v, j)) {
        call $ExecFailureAbort();
        return;
    }
    m' := $UpdateMutation(m, SwapVec(v, i, j));
}

function {:inline} $1_vector_$swap'$1_governance_proposal_GovernanceProposal'(v: Vec ($1_governance_proposal_GovernanceProposal), i: int, j: int): Vec ($1_governance_proposal_GovernanceProposal) {
    SwapVec(v, i, j)
}

procedure {:inline 1} $1_vector_remove'$1_governance_proposal_GovernanceProposal'(m: $Mutation (Vec ($1_governance_proposal_GovernanceProposal)), i: int) returns (e: $1_governance_proposal_GovernanceProposal, m': $Mutation (Vec ($1_governance_proposal_GovernanceProposal)))
{
    var v: Vec ($1_governance_proposal_GovernanceProposal);

    v := $Dereference(m);

    if (!InRangeVec(v, i)) {
        call $ExecFailureAbort();
        return;
    }
    e := ReadVec(v, i);
    m' := $UpdateMutation(m, RemoveAtVec(v, i));
}

procedure {:inline 1} $1_vector_swap_remove'$1_governance_proposal_GovernanceProposal'(m: $Mutation (Vec ($1_governance_proposal_GovernanceProposal)), i: int) returns (e: $1_governance_proposal_GovernanceProposal, m': $Mutation (Vec ($1_governance_proposal_GovernanceProposal)))
{
    var len: int;
    var v: Vec ($1_governance_proposal_GovernanceProposal);

    v := $Dereference(m);
    len := LenVec(v);
    if (!InRangeVec(v, i)) {
        call $ExecFailureAbort();
        return;
    }
    e := ReadVec(v, i);
    m' := $UpdateMutation(m, RemoveVec(SwapVec(v, i, len-1)));
}

procedure {:inline 1} $1_vector_contains'$1_governance_proposal_GovernanceProposal'(v: Vec ($1_governance_proposal_GovernanceProposal), e: $1_governance_proposal_GovernanceProposal) returns (res: bool)  {
    res := $ContainsVec'$1_governance_proposal_GovernanceProposal'(v, e);
}

procedure {:inline 1}
$1_vector_index_of'$1_governance_proposal_GovernanceProposal'(v: Vec ($1_governance_proposal_GovernanceProposal), e: $1_governance_proposal_GovernanceProposal) returns (res1: bool, res2: int) {
    res2 := $IndexOfVec'$1_governance_proposal_GovernanceProposal'(v, e);
    if (res2 >= 0) {
        res1 := true;
    } else {
        res1 := false;
        res2 := 0;
    }
}


// ----------------------------------------------------------------------------------
// Native Vector implementation for element type `$1_stake_IndividualValidatorPerformance`

// Not inlined. It appears faster this way.
function $IsEqual'vec'$1_stake_IndividualValidatorPerformance''(v1: Vec ($1_stake_IndividualValidatorPerformance), v2: Vec ($1_stake_IndividualValidatorPerformance)): bool {
    LenVec(v1) == LenVec(v2) &&
    (forall i: int:: InRangeVec(v1, i) ==> $IsEqual'$1_stake_IndividualValidatorPerformance'(ReadVec(v1, i), ReadVec(v2, i)))
}

// Not inlined.
function $IsPrefix'vec'$1_stake_IndividualValidatorPerformance''(v: Vec ($1_stake_IndividualValidatorPerformance), prefix: Vec ($1_stake_IndividualValidatorPerformance)): bool {
    LenVec(v) >= LenVec(prefix) &&
    (forall i: int:: InRangeVec(prefix, i) ==> $IsEqual'$1_stake_IndividualValidatorPerformance'(ReadVec(v, i), ReadVec(prefix, i)))
}

// Not inlined.
function $IsSuffix'vec'$1_stake_IndividualValidatorPerformance''(v: Vec ($1_stake_IndividualValidatorPerformance), suffix: Vec ($1_stake_IndividualValidatorPerformance)): bool {
    LenVec(v) >= LenVec(suffix) &&
    (forall i: int:: InRangeVec(suffix, i) ==> $IsEqual'$1_stake_IndividualValidatorPerformance'(ReadVec(v, LenVec(v) - LenVec(suffix) + i), ReadVec(suffix, i)))
}

// Not inlined.
function $IsValid'vec'$1_stake_IndividualValidatorPerformance''(v: Vec ($1_stake_IndividualValidatorPerformance)): bool {
    $IsValid'u64'(LenVec(v)) &&
    (forall i: int:: InRangeVec(v, i) ==> $IsValid'$1_stake_IndividualValidatorPerformance'(ReadVec(v, i)))
}


function {:inline} $ContainsVec'$1_stake_IndividualValidatorPerformance'(v: Vec ($1_stake_IndividualValidatorPerformance), e: $1_stake_IndividualValidatorPerformance): bool {
    (exists i: int :: $IsValid'u64'(i) && InRangeVec(v, i) && $IsEqual'$1_stake_IndividualValidatorPerformance'(ReadVec(v, i), e))
}

function $IndexOfVec'$1_stake_IndividualValidatorPerformance'(v: Vec ($1_stake_IndividualValidatorPerformance), e: $1_stake_IndividualValidatorPerformance): int;
axiom (forall v: Vec ($1_stake_IndividualValidatorPerformance), e: $1_stake_IndividualValidatorPerformance:: {$IndexOfVec'$1_stake_IndividualValidatorPerformance'(v, e)}
    (var i := $IndexOfVec'$1_stake_IndividualValidatorPerformance'(v, e);
     if (!$ContainsVec'$1_stake_IndividualValidatorPerformance'(v, e)) then i == -1
     else $IsValid'u64'(i) && InRangeVec(v, i) && $IsEqual'$1_stake_IndividualValidatorPerformance'(ReadVec(v, i), e) &&
        (forall j: int :: $IsValid'u64'(j) && j >= 0 && j < i ==> !$IsEqual'$1_stake_IndividualValidatorPerformance'(ReadVec(v, j), e))));


function {:inline} $RangeVec'$1_stake_IndividualValidatorPerformance'(v: Vec ($1_stake_IndividualValidatorPerformance)): $Range {
    $Range(0, LenVec(v))
}


function {:inline} $EmptyVec'$1_stake_IndividualValidatorPerformance'(): Vec ($1_stake_IndividualValidatorPerformance) {
    EmptyVec()
}

procedure {:inline 1} $1_vector_empty'$1_stake_IndividualValidatorPerformance'() returns (v: Vec ($1_stake_IndividualValidatorPerformance)) {
    v := EmptyVec();
}

function {:inline} $1_vector_$empty'$1_stake_IndividualValidatorPerformance'(): Vec ($1_stake_IndividualValidatorPerformance) {
    EmptyVec()
}

procedure {:inline 1} $1_vector_is_empty'$1_stake_IndividualValidatorPerformance'(v: Vec ($1_stake_IndividualValidatorPerformance)) returns (b: bool) {
    b := IsEmptyVec(v);
}

procedure {:inline 1} $1_vector_push_back'$1_stake_IndividualValidatorPerformance'(m: $Mutation (Vec ($1_stake_IndividualValidatorPerformance)), val: $1_stake_IndividualValidatorPerformance) returns (m': $Mutation (Vec ($1_stake_IndividualValidatorPerformance))) {
    m' := $UpdateMutation(m, ExtendVec($Dereference(m), val));
}

function {:inline} $1_vector_$push_back'$1_stake_IndividualValidatorPerformance'(v: Vec ($1_stake_IndividualValidatorPerformance), val: $1_stake_IndividualValidatorPerformance): Vec ($1_stake_IndividualValidatorPerformance) {
    ExtendVec(v, val)
}

procedure {:inline 1} $1_vector_pop_back'$1_stake_IndividualValidatorPerformance'(m: $Mutation (Vec ($1_stake_IndividualValidatorPerformance))) returns (e: $1_stake_IndividualValidatorPerformance, m': $Mutation (Vec ($1_stake_IndividualValidatorPerformance))) {
    var v: Vec ($1_stake_IndividualValidatorPerformance);
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

procedure {:inline 1} $1_vector_append'$1_stake_IndividualValidatorPerformance'(m: $Mutation (Vec ($1_stake_IndividualValidatorPerformance)), other: Vec ($1_stake_IndividualValidatorPerformance)) returns (m': $Mutation (Vec ($1_stake_IndividualValidatorPerformance))) {
    m' := $UpdateMutation(m, ConcatVec($Dereference(m), other));
}

procedure {:inline 1} $1_vector_reverse'$1_stake_IndividualValidatorPerformance'(m: $Mutation (Vec ($1_stake_IndividualValidatorPerformance))) returns (m': $Mutation (Vec ($1_stake_IndividualValidatorPerformance))) {
    m' := $UpdateMutation(m, ReverseVec($Dereference(m)));
}

procedure {:inline 1} $1_vector_reverse_append'$1_stake_IndividualValidatorPerformance'(m: $Mutation (Vec ($1_stake_IndividualValidatorPerformance)), other: Vec ($1_stake_IndividualValidatorPerformance)) returns (m': $Mutation (Vec ($1_stake_IndividualValidatorPerformance))) {
    m' := $UpdateMutation(m, ConcatVec($Dereference(m), ReverseVec(other)));
}

procedure {:inline 1} $1_vector_trim_reverse'$1_stake_IndividualValidatorPerformance'(m: $Mutation (Vec ($1_stake_IndividualValidatorPerformance)), new_len: int) returns (v: (Vec ($1_stake_IndividualValidatorPerformance)), m': $Mutation (Vec ($1_stake_IndividualValidatorPerformance))) {
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

procedure {:inline 1} $1_vector_trim'$1_stake_IndividualValidatorPerformance'(m: $Mutation (Vec ($1_stake_IndividualValidatorPerformance)), new_len: int) returns (v: (Vec ($1_stake_IndividualValidatorPerformance)), m': $Mutation (Vec ($1_stake_IndividualValidatorPerformance))) {
    var len: int;
    v := $Dereference(m);
    if (LenVec(v) < new_len) {
        call $ExecFailureAbort();
        return;
    }
    v := SliceVec(v, new_len, LenVec(v));
    m' := $UpdateMutation(m, SliceVec($Dereference(m), 0, new_len));
}

procedure {:inline 1} $1_vector_reverse_slice'$1_stake_IndividualValidatorPerformance'(m: $Mutation (Vec ($1_stake_IndividualValidatorPerformance)), left: int, right: int) returns (m': $Mutation (Vec ($1_stake_IndividualValidatorPerformance))) {
    var left_vec: Vec ($1_stake_IndividualValidatorPerformance);
    var mid_vec: Vec ($1_stake_IndividualValidatorPerformance);
    var right_vec: Vec ($1_stake_IndividualValidatorPerformance);
    var v: Vec ($1_stake_IndividualValidatorPerformance);
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

procedure {:inline 1} $1_vector_rotate'$1_stake_IndividualValidatorPerformance'(m: $Mutation (Vec ($1_stake_IndividualValidatorPerformance)), rot: int) returns (n: int, m': $Mutation (Vec ($1_stake_IndividualValidatorPerformance))) {
    var v: Vec ($1_stake_IndividualValidatorPerformance);
    var len: int;
    var left_vec: Vec ($1_stake_IndividualValidatorPerformance);
    var right_vec: Vec ($1_stake_IndividualValidatorPerformance);
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

procedure {:inline 1} $1_vector_rotate_slice'$1_stake_IndividualValidatorPerformance'(m: $Mutation (Vec ($1_stake_IndividualValidatorPerformance)), left: int, rot: int, right: int) returns (n: int, m': $Mutation (Vec ($1_stake_IndividualValidatorPerformance))) {
    var left_vec: Vec ($1_stake_IndividualValidatorPerformance);
    var mid_vec: Vec ($1_stake_IndividualValidatorPerformance);
    var right_vec: Vec ($1_stake_IndividualValidatorPerformance);
    var mid_left_vec: Vec ($1_stake_IndividualValidatorPerformance);
    var mid_right_vec: Vec ($1_stake_IndividualValidatorPerformance);
    var v: Vec ($1_stake_IndividualValidatorPerformance);
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

procedure {:inline 1} $1_vector_insert'$1_stake_IndividualValidatorPerformance'(m: $Mutation (Vec ($1_stake_IndividualValidatorPerformance)), i: int, e: $1_stake_IndividualValidatorPerformance) returns (m': $Mutation (Vec ($1_stake_IndividualValidatorPerformance))) {
    var left_vec: Vec ($1_stake_IndividualValidatorPerformance);
    var right_vec: Vec ($1_stake_IndividualValidatorPerformance);
    var v: Vec ($1_stake_IndividualValidatorPerformance);
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

procedure {:inline 1} $1_vector_length'$1_stake_IndividualValidatorPerformance'(v: Vec ($1_stake_IndividualValidatorPerformance)) returns (l: int) {
    l := LenVec(v);
}

function {:inline} $1_vector_$length'$1_stake_IndividualValidatorPerformance'(v: Vec ($1_stake_IndividualValidatorPerformance)): int {
    LenVec(v)
}

procedure {:inline 1} $1_vector_borrow'$1_stake_IndividualValidatorPerformance'(v: Vec ($1_stake_IndividualValidatorPerformance), i: int) returns (dst: $1_stake_IndividualValidatorPerformance) {
    if (!InRangeVec(v, i)) {
        call $ExecFailureAbort();
        return;
    }
    dst := ReadVec(v, i);
}

function {:inline} $1_vector_$borrow'$1_stake_IndividualValidatorPerformance'(v: Vec ($1_stake_IndividualValidatorPerformance), i: int): $1_stake_IndividualValidatorPerformance {
    ReadVec(v, i)
}

procedure {:inline 1} $1_vector_borrow_mut'$1_stake_IndividualValidatorPerformance'(m: $Mutation (Vec ($1_stake_IndividualValidatorPerformance)), index: int)
returns (dst: $Mutation ($1_stake_IndividualValidatorPerformance), m': $Mutation (Vec ($1_stake_IndividualValidatorPerformance)))
{
    var v: Vec ($1_stake_IndividualValidatorPerformance);
    v := $Dereference(m);
    if (!InRangeVec(v, index)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Mutation(l#$Mutation(m), ExtendVec(p#$Mutation(m), index), ReadVec(v, index));
    m' := m;
}

function {:inline} $1_vector_$borrow_mut'$1_stake_IndividualValidatorPerformance'(v: Vec ($1_stake_IndividualValidatorPerformance), i: int): $1_stake_IndividualValidatorPerformance {
    ReadVec(v, i)
}

procedure {:inline 1} $1_vector_destroy_empty'$1_stake_IndividualValidatorPerformance'(v: Vec ($1_stake_IndividualValidatorPerformance)) {
    if (!IsEmptyVec(v)) {
      call $ExecFailureAbort();
    }
}

procedure {:inline 1} $1_vector_swap'$1_stake_IndividualValidatorPerformance'(m: $Mutation (Vec ($1_stake_IndividualValidatorPerformance)), i: int, j: int) returns (m': $Mutation (Vec ($1_stake_IndividualValidatorPerformance)))
{
    var v: Vec ($1_stake_IndividualValidatorPerformance);
    v := $Dereference(m);
    if (!InRangeVec(v, i) || !InRangeVec(v, j)) {
        call $ExecFailureAbort();
        return;
    }
    m' := $UpdateMutation(m, SwapVec(v, i, j));
}

function {:inline} $1_vector_$swap'$1_stake_IndividualValidatorPerformance'(v: Vec ($1_stake_IndividualValidatorPerformance), i: int, j: int): Vec ($1_stake_IndividualValidatorPerformance) {
    SwapVec(v, i, j)
}

procedure {:inline 1} $1_vector_remove'$1_stake_IndividualValidatorPerformance'(m: $Mutation (Vec ($1_stake_IndividualValidatorPerformance)), i: int) returns (e: $1_stake_IndividualValidatorPerformance, m': $Mutation (Vec ($1_stake_IndividualValidatorPerformance)))
{
    var v: Vec ($1_stake_IndividualValidatorPerformance);

    v := $Dereference(m);

    if (!InRangeVec(v, i)) {
        call $ExecFailureAbort();
        return;
    }
    e := ReadVec(v, i);
    m' := $UpdateMutation(m, RemoveAtVec(v, i));
}

procedure {:inline 1} $1_vector_swap_remove'$1_stake_IndividualValidatorPerformance'(m: $Mutation (Vec ($1_stake_IndividualValidatorPerformance)), i: int) returns (e: $1_stake_IndividualValidatorPerformance, m': $Mutation (Vec ($1_stake_IndividualValidatorPerformance)))
{
    var len: int;
    var v: Vec ($1_stake_IndividualValidatorPerformance);

    v := $Dereference(m);
    len := LenVec(v);
    if (!InRangeVec(v, i)) {
        call $ExecFailureAbort();
        return;
    }
    e := ReadVec(v, i);
    m' := $UpdateMutation(m, RemoveVec(SwapVec(v, i, len-1)));
}

procedure {:inline 1} $1_vector_contains'$1_stake_IndividualValidatorPerformance'(v: Vec ($1_stake_IndividualValidatorPerformance), e: $1_stake_IndividualValidatorPerformance) returns (res: bool)  {
    res := $ContainsVec'$1_stake_IndividualValidatorPerformance'(v, e);
}

procedure {:inline 1}
$1_vector_index_of'$1_stake_IndividualValidatorPerformance'(v: Vec ($1_stake_IndividualValidatorPerformance), e: $1_stake_IndividualValidatorPerformance) returns (res1: bool, res2: int) {
    res2 := $IndexOfVec'$1_stake_IndividualValidatorPerformance'(v, e);
    if (res2 >= 0) {
        res1 := true;
    } else {
        res1 := false;
        res2 := 0;
    }
}


// ----------------------------------------------------------------------------------
// Native Vector implementation for element type `$1_stake_ValidatorInfo`

// Not inlined. It appears faster this way.
function $IsEqual'vec'$1_stake_ValidatorInfo''(v1: Vec ($1_stake_ValidatorInfo), v2: Vec ($1_stake_ValidatorInfo)): bool {
    LenVec(v1) == LenVec(v2) &&
    (forall i: int:: InRangeVec(v1, i) ==> $IsEqual'$1_stake_ValidatorInfo'(ReadVec(v1, i), ReadVec(v2, i)))
}

// Not inlined.
function $IsPrefix'vec'$1_stake_ValidatorInfo''(v: Vec ($1_stake_ValidatorInfo), prefix: Vec ($1_stake_ValidatorInfo)): bool {
    LenVec(v) >= LenVec(prefix) &&
    (forall i: int:: InRangeVec(prefix, i) ==> $IsEqual'$1_stake_ValidatorInfo'(ReadVec(v, i), ReadVec(prefix, i)))
}

// Not inlined.
function $IsSuffix'vec'$1_stake_ValidatorInfo''(v: Vec ($1_stake_ValidatorInfo), suffix: Vec ($1_stake_ValidatorInfo)): bool {
    LenVec(v) >= LenVec(suffix) &&
    (forall i: int:: InRangeVec(suffix, i) ==> $IsEqual'$1_stake_ValidatorInfo'(ReadVec(v, LenVec(v) - LenVec(suffix) + i), ReadVec(suffix, i)))
}

// Not inlined.
function $IsValid'vec'$1_stake_ValidatorInfo''(v: Vec ($1_stake_ValidatorInfo)): bool {
    $IsValid'u64'(LenVec(v)) &&
    (forall i: int:: InRangeVec(v, i) ==> $IsValid'$1_stake_ValidatorInfo'(ReadVec(v, i)))
}


function {:inline} $ContainsVec'$1_stake_ValidatorInfo'(v: Vec ($1_stake_ValidatorInfo), e: $1_stake_ValidatorInfo): bool {
    (exists i: int :: $IsValid'u64'(i) && InRangeVec(v, i) && $IsEqual'$1_stake_ValidatorInfo'(ReadVec(v, i), e))
}

function $IndexOfVec'$1_stake_ValidatorInfo'(v: Vec ($1_stake_ValidatorInfo), e: $1_stake_ValidatorInfo): int;
axiom (forall v: Vec ($1_stake_ValidatorInfo), e: $1_stake_ValidatorInfo:: {$IndexOfVec'$1_stake_ValidatorInfo'(v, e)}
    (var i := $IndexOfVec'$1_stake_ValidatorInfo'(v, e);
     if (!$ContainsVec'$1_stake_ValidatorInfo'(v, e)) then i == -1
     else $IsValid'u64'(i) && InRangeVec(v, i) && $IsEqual'$1_stake_ValidatorInfo'(ReadVec(v, i), e) &&
        (forall j: int :: $IsValid'u64'(j) && j >= 0 && j < i ==> !$IsEqual'$1_stake_ValidatorInfo'(ReadVec(v, j), e))));


function {:inline} $RangeVec'$1_stake_ValidatorInfo'(v: Vec ($1_stake_ValidatorInfo)): $Range {
    $Range(0, LenVec(v))
}


function {:inline} $EmptyVec'$1_stake_ValidatorInfo'(): Vec ($1_stake_ValidatorInfo) {
    EmptyVec()
}

procedure {:inline 1} $1_vector_empty'$1_stake_ValidatorInfo'() returns (v: Vec ($1_stake_ValidatorInfo)) {
    v := EmptyVec();
}

function {:inline} $1_vector_$empty'$1_stake_ValidatorInfo'(): Vec ($1_stake_ValidatorInfo) {
    EmptyVec()
}

procedure {:inline 1} $1_vector_is_empty'$1_stake_ValidatorInfo'(v: Vec ($1_stake_ValidatorInfo)) returns (b: bool) {
    b := IsEmptyVec(v);
}

procedure {:inline 1} $1_vector_push_back'$1_stake_ValidatorInfo'(m: $Mutation (Vec ($1_stake_ValidatorInfo)), val: $1_stake_ValidatorInfo) returns (m': $Mutation (Vec ($1_stake_ValidatorInfo))) {
    m' := $UpdateMutation(m, ExtendVec($Dereference(m), val));
}

function {:inline} $1_vector_$push_back'$1_stake_ValidatorInfo'(v: Vec ($1_stake_ValidatorInfo), val: $1_stake_ValidatorInfo): Vec ($1_stake_ValidatorInfo) {
    ExtendVec(v, val)
}

procedure {:inline 1} $1_vector_pop_back'$1_stake_ValidatorInfo'(m: $Mutation (Vec ($1_stake_ValidatorInfo))) returns (e: $1_stake_ValidatorInfo, m': $Mutation (Vec ($1_stake_ValidatorInfo))) {
    var v: Vec ($1_stake_ValidatorInfo);
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

procedure {:inline 1} $1_vector_append'$1_stake_ValidatorInfo'(m: $Mutation (Vec ($1_stake_ValidatorInfo)), other: Vec ($1_stake_ValidatorInfo)) returns (m': $Mutation (Vec ($1_stake_ValidatorInfo))) {
    m' := $UpdateMutation(m, ConcatVec($Dereference(m), other));
}

procedure {:inline 1} $1_vector_reverse'$1_stake_ValidatorInfo'(m: $Mutation (Vec ($1_stake_ValidatorInfo))) returns (m': $Mutation (Vec ($1_stake_ValidatorInfo))) {
    m' := $UpdateMutation(m, ReverseVec($Dereference(m)));
}

procedure {:inline 1} $1_vector_reverse_append'$1_stake_ValidatorInfo'(m: $Mutation (Vec ($1_stake_ValidatorInfo)), other: Vec ($1_stake_ValidatorInfo)) returns (m': $Mutation (Vec ($1_stake_ValidatorInfo))) {
    m' := $UpdateMutation(m, ConcatVec($Dereference(m), ReverseVec(other)));
}

procedure {:inline 1} $1_vector_trim_reverse'$1_stake_ValidatorInfo'(m: $Mutation (Vec ($1_stake_ValidatorInfo)), new_len: int) returns (v: (Vec ($1_stake_ValidatorInfo)), m': $Mutation (Vec ($1_stake_ValidatorInfo))) {
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

procedure {:inline 1} $1_vector_trim'$1_stake_ValidatorInfo'(m: $Mutation (Vec ($1_stake_ValidatorInfo)), new_len: int) returns (v: (Vec ($1_stake_ValidatorInfo)), m': $Mutation (Vec ($1_stake_ValidatorInfo))) {
    var len: int;
    v := $Dereference(m);
    if (LenVec(v) < new_len) {
        call $ExecFailureAbort();
        return;
    }
    v := SliceVec(v, new_len, LenVec(v));
    m' := $UpdateMutation(m, SliceVec($Dereference(m), 0, new_len));
}

procedure {:inline 1} $1_vector_reverse_slice'$1_stake_ValidatorInfo'(m: $Mutation (Vec ($1_stake_ValidatorInfo)), left: int, right: int) returns (m': $Mutation (Vec ($1_stake_ValidatorInfo))) {
    var left_vec: Vec ($1_stake_ValidatorInfo);
    var mid_vec: Vec ($1_stake_ValidatorInfo);
    var right_vec: Vec ($1_stake_ValidatorInfo);
    var v: Vec ($1_stake_ValidatorInfo);
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

procedure {:inline 1} $1_vector_rotate'$1_stake_ValidatorInfo'(m: $Mutation (Vec ($1_stake_ValidatorInfo)), rot: int) returns (n: int, m': $Mutation (Vec ($1_stake_ValidatorInfo))) {
    var v: Vec ($1_stake_ValidatorInfo);
    var len: int;
    var left_vec: Vec ($1_stake_ValidatorInfo);
    var right_vec: Vec ($1_stake_ValidatorInfo);
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

procedure {:inline 1} $1_vector_rotate_slice'$1_stake_ValidatorInfo'(m: $Mutation (Vec ($1_stake_ValidatorInfo)), left: int, rot: int, right: int) returns (n: int, m': $Mutation (Vec ($1_stake_ValidatorInfo))) {
    var left_vec: Vec ($1_stake_ValidatorInfo);
    var mid_vec: Vec ($1_stake_ValidatorInfo);
    var right_vec: Vec ($1_stake_ValidatorInfo);
    var mid_left_vec: Vec ($1_stake_ValidatorInfo);
    var mid_right_vec: Vec ($1_stake_ValidatorInfo);
    var v: Vec ($1_stake_ValidatorInfo);
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

procedure {:inline 1} $1_vector_insert'$1_stake_ValidatorInfo'(m: $Mutation (Vec ($1_stake_ValidatorInfo)), i: int, e: $1_stake_ValidatorInfo) returns (m': $Mutation (Vec ($1_stake_ValidatorInfo))) {
    var left_vec: Vec ($1_stake_ValidatorInfo);
    var right_vec: Vec ($1_stake_ValidatorInfo);
    var v: Vec ($1_stake_ValidatorInfo);
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

procedure {:inline 1} $1_vector_length'$1_stake_ValidatorInfo'(v: Vec ($1_stake_ValidatorInfo)) returns (l: int) {
    l := LenVec(v);
}

function {:inline} $1_vector_$length'$1_stake_ValidatorInfo'(v: Vec ($1_stake_ValidatorInfo)): int {
    LenVec(v)
}

procedure {:inline 1} $1_vector_borrow'$1_stake_ValidatorInfo'(v: Vec ($1_stake_ValidatorInfo), i: int) returns (dst: $1_stake_ValidatorInfo) {
    if (!InRangeVec(v, i)) {
        call $ExecFailureAbort();
        return;
    }
    dst := ReadVec(v, i);
}

function {:inline} $1_vector_$borrow'$1_stake_ValidatorInfo'(v: Vec ($1_stake_ValidatorInfo), i: int): $1_stake_ValidatorInfo {
    ReadVec(v, i)
}

procedure {:inline 1} $1_vector_borrow_mut'$1_stake_ValidatorInfo'(m: $Mutation (Vec ($1_stake_ValidatorInfo)), index: int)
returns (dst: $Mutation ($1_stake_ValidatorInfo), m': $Mutation (Vec ($1_stake_ValidatorInfo)))
{
    var v: Vec ($1_stake_ValidatorInfo);
    v := $Dereference(m);
    if (!InRangeVec(v, index)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Mutation(l#$Mutation(m), ExtendVec(p#$Mutation(m), index), ReadVec(v, index));
    m' := m;
}

function {:inline} $1_vector_$borrow_mut'$1_stake_ValidatorInfo'(v: Vec ($1_stake_ValidatorInfo), i: int): $1_stake_ValidatorInfo {
    ReadVec(v, i)
}

procedure {:inline 1} $1_vector_destroy_empty'$1_stake_ValidatorInfo'(v: Vec ($1_stake_ValidatorInfo)) {
    if (!IsEmptyVec(v)) {
      call $ExecFailureAbort();
    }
}

procedure {:inline 1} $1_vector_swap'$1_stake_ValidatorInfo'(m: $Mutation (Vec ($1_stake_ValidatorInfo)), i: int, j: int) returns (m': $Mutation (Vec ($1_stake_ValidatorInfo)))
{
    var v: Vec ($1_stake_ValidatorInfo);
    v := $Dereference(m);
    if (!InRangeVec(v, i) || !InRangeVec(v, j)) {
        call $ExecFailureAbort();
        return;
    }
    m' := $UpdateMutation(m, SwapVec(v, i, j));
}

function {:inline} $1_vector_$swap'$1_stake_ValidatorInfo'(v: Vec ($1_stake_ValidatorInfo), i: int, j: int): Vec ($1_stake_ValidatorInfo) {
    SwapVec(v, i, j)
}

procedure {:inline 1} $1_vector_remove'$1_stake_ValidatorInfo'(m: $Mutation (Vec ($1_stake_ValidatorInfo)), i: int) returns (e: $1_stake_ValidatorInfo, m': $Mutation (Vec ($1_stake_ValidatorInfo)))
{
    var v: Vec ($1_stake_ValidatorInfo);

    v := $Dereference(m);

    if (!InRangeVec(v, i)) {
        call $ExecFailureAbort();
        return;
    }
    e := ReadVec(v, i);
    m' := $UpdateMutation(m, RemoveAtVec(v, i));
}

procedure {:inline 1} $1_vector_swap_remove'$1_stake_ValidatorInfo'(m: $Mutation (Vec ($1_stake_ValidatorInfo)), i: int) returns (e: $1_stake_ValidatorInfo, m': $Mutation (Vec ($1_stake_ValidatorInfo)))
{
    var len: int;
    var v: Vec ($1_stake_ValidatorInfo);

    v := $Dereference(m);
    len := LenVec(v);
    if (!InRangeVec(v, i)) {
        call $ExecFailureAbort();
        return;
    }
    e := ReadVec(v, i);
    m' := $UpdateMutation(m, RemoveVec(SwapVec(v, i, len-1)));
}

procedure {:inline 1} $1_vector_contains'$1_stake_ValidatorInfo'(v: Vec ($1_stake_ValidatorInfo), e: $1_stake_ValidatorInfo) returns (res: bool)  {
    res := $ContainsVec'$1_stake_ValidatorInfo'(v, e);
}

procedure {:inline 1}
$1_vector_index_of'$1_stake_ValidatorInfo'(v: Vec ($1_stake_ValidatorInfo), e: $1_stake_ValidatorInfo) returns (res1: bool, res2: int) {
    res2 := $IndexOfVec'$1_stake_ValidatorInfo'(v, e);
    if (res2 >= 0) {
        res1 := true;
    } else {
        res1 := false;
        res2 := 0;
    }
}


// ----------------------------------------------------------------------------------
// Native Vector implementation for element type `$1_storage_gas_Point`

// Not inlined. It appears faster this way.
function $IsEqual'vec'$1_storage_gas_Point''(v1: Vec ($1_storage_gas_Point), v2: Vec ($1_storage_gas_Point)): bool {
    LenVec(v1) == LenVec(v2) &&
    (forall i: int:: InRangeVec(v1, i) ==> $IsEqual'$1_storage_gas_Point'(ReadVec(v1, i), ReadVec(v2, i)))
}

// Not inlined.
function $IsPrefix'vec'$1_storage_gas_Point''(v: Vec ($1_storage_gas_Point), prefix: Vec ($1_storage_gas_Point)): bool {
    LenVec(v) >= LenVec(prefix) &&
    (forall i: int:: InRangeVec(prefix, i) ==> $IsEqual'$1_storage_gas_Point'(ReadVec(v, i), ReadVec(prefix, i)))
}

// Not inlined.
function $IsSuffix'vec'$1_storage_gas_Point''(v: Vec ($1_storage_gas_Point), suffix: Vec ($1_storage_gas_Point)): bool {
    LenVec(v) >= LenVec(suffix) &&
    (forall i: int:: InRangeVec(suffix, i) ==> $IsEqual'$1_storage_gas_Point'(ReadVec(v, LenVec(v) - LenVec(suffix) + i), ReadVec(suffix, i)))
}

// Not inlined.
function $IsValid'vec'$1_storage_gas_Point''(v: Vec ($1_storage_gas_Point)): bool {
    $IsValid'u64'(LenVec(v)) &&
    (forall i: int:: InRangeVec(v, i) ==> $IsValid'$1_storage_gas_Point'(ReadVec(v, i)))
}


function {:inline} $ContainsVec'$1_storage_gas_Point'(v: Vec ($1_storage_gas_Point), e: $1_storage_gas_Point): bool {
    (exists i: int :: $IsValid'u64'(i) && InRangeVec(v, i) && $IsEqual'$1_storage_gas_Point'(ReadVec(v, i), e))
}

function $IndexOfVec'$1_storage_gas_Point'(v: Vec ($1_storage_gas_Point), e: $1_storage_gas_Point): int;
axiom (forall v: Vec ($1_storage_gas_Point), e: $1_storage_gas_Point:: {$IndexOfVec'$1_storage_gas_Point'(v, e)}
    (var i := $IndexOfVec'$1_storage_gas_Point'(v, e);
     if (!$ContainsVec'$1_storage_gas_Point'(v, e)) then i == -1
     else $IsValid'u64'(i) && InRangeVec(v, i) && $IsEqual'$1_storage_gas_Point'(ReadVec(v, i), e) &&
        (forall j: int :: $IsValid'u64'(j) && j >= 0 && j < i ==> !$IsEqual'$1_storage_gas_Point'(ReadVec(v, j), e))));


function {:inline} $RangeVec'$1_storage_gas_Point'(v: Vec ($1_storage_gas_Point)): $Range {
    $Range(0, LenVec(v))
}


function {:inline} $EmptyVec'$1_storage_gas_Point'(): Vec ($1_storage_gas_Point) {
    EmptyVec()
}

procedure {:inline 1} $1_vector_empty'$1_storage_gas_Point'() returns (v: Vec ($1_storage_gas_Point)) {
    v := EmptyVec();
}

function {:inline} $1_vector_$empty'$1_storage_gas_Point'(): Vec ($1_storage_gas_Point) {
    EmptyVec()
}

procedure {:inline 1} $1_vector_is_empty'$1_storage_gas_Point'(v: Vec ($1_storage_gas_Point)) returns (b: bool) {
    b := IsEmptyVec(v);
}

procedure {:inline 1} $1_vector_push_back'$1_storage_gas_Point'(m: $Mutation (Vec ($1_storage_gas_Point)), val: $1_storage_gas_Point) returns (m': $Mutation (Vec ($1_storage_gas_Point))) {
    m' := $UpdateMutation(m, ExtendVec($Dereference(m), val));
}

function {:inline} $1_vector_$push_back'$1_storage_gas_Point'(v: Vec ($1_storage_gas_Point), val: $1_storage_gas_Point): Vec ($1_storage_gas_Point) {
    ExtendVec(v, val)
}

procedure {:inline 1} $1_vector_pop_back'$1_storage_gas_Point'(m: $Mutation (Vec ($1_storage_gas_Point))) returns (e: $1_storage_gas_Point, m': $Mutation (Vec ($1_storage_gas_Point))) {
    var v: Vec ($1_storage_gas_Point);
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

procedure {:inline 1} $1_vector_append'$1_storage_gas_Point'(m: $Mutation (Vec ($1_storage_gas_Point)), other: Vec ($1_storage_gas_Point)) returns (m': $Mutation (Vec ($1_storage_gas_Point))) {
    m' := $UpdateMutation(m, ConcatVec($Dereference(m), other));
}

procedure {:inline 1} $1_vector_reverse'$1_storage_gas_Point'(m: $Mutation (Vec ($1_storage_gas_Point))) returns (m': $Mutation (Vec ($1_storage_gas_Point))) {
    m' := $UpdateMutation(m, ReverseVec($Dereference(m)));
}

procedure {:inline 1} $1_vector_reverse_append'$1_storage_gas_Point'(m: $Mutation (Vec ($1_storage_gas_Point)), other: Vec ($1_storage_gas_Point)) returns (m': $Mutation (Vec ($1_storage_gas_Point))) {
    m' := $UpdateMutation(m, ConcatVec($Dereference(m), ReverseVec(other)));
}

procedure {:inline 1} $1_vector_trim_reverse'$1_storage_gas_Point'(m: $Mutation (Vec ($1_storage_gas_Point)), new_len: int) returns (v: (Vec ($1_storage_gas_Point)), m': $Mutation (Vec ($1_storage_gas_Point))) {
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

procedure {:inline 1} $1_vector_trim'$1_storage_gas_Point'(m: $Mutation (Vec ($1_storage_gas_Point)), new_len: int) returns (v: (Vec ($1_storage_gas_Point)), m': $Mutation (Vec ($1_storage_gas_Point))) {
    var len: int;
    v := $Dereference(m);
    if (LenVec(v) < new_len) {
        call $ExecFailureAbort();
        return;
    }
    v := SliceVec(v, new_len, LenVec(v));
    m' := $UpdateMutation(m, SliceVec($Dereference(m), 0, new_len));
}

procedure {:inline 1} $1_vector_reverse_slice'$1_storage_gas_Point'(m: $Mutation (Vec ($1_storage_gas_Point)), left: int, right: int) returns (m': $Mutation (Vec ($1_storage_gas_Point))) {
    var left_vec: Vec ($1_storage_gas_Point);
    var mid_vec: Vec ($1_storage_gas_Point);
    var right_vec: Vec ($1_storage_gas_Point);
    var v: Vec ($1_storage_gas_Point);
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

procedure {:inline 1} $1_vector_rotate'$1_storage_gas_Point'(m: $Mutation (Vec ($1_storage_gas_Point)), rot: int) returns (n: int, m': $Mutation (Vec ($1_storage_gas_Point))) {
    var v: Vec ($1_storage_gas_Point);
    var len: int;
    var left_vec: Vec ($1_storage_gas_Point);
    var right_vec: Vec ($1_storage_gas_Point);
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

procedure {:inline 1} $1_vector_rotate_slice'$1_storage_gas_Point'(m: $Mutation (Vec ($1_storage_gas_Point)), left: int, rot: int, right: int) returns (n: int, m': $Mutation (Vec ($1_storage_gas_Point))) {
    var left_vec: Vec ($1_storage_gas_Point);
    var mid_vec: Vec ($1_storage_gas_Point);
    var right_vec: Vec ($1_storage_gas_Point);
    var mid_left_vec: Vec ($1_storage_gas_Point);
    var mid_right_vec: Vec ($1_storage_gas_Point);
    var v: Vec ($1_storage_gas_Point);
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

procedure {:inline 1} $1_vector_insert'$1_storage_gas_Point'(m: $Mutation (Vec ($1_storage_gas_Point)), i: int, e: $1_storage_gas_Point) returns (m': $Mutation (Vec ($1_storage_gas_Point))) {
    var left_vec: Vec ($1_storage_gas_Point);
    var right_vec: Vec ($1_storage_gas_Point);
    var v: Vec ($1_storage_gas_Point);
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

procedure {:inline 1} $1_vector_length'$1_storage_gas_Point'(v: Vec ($1_storage_gas_Point)) returns (l: int) {
    l := LenVec(v);
}

function {:inline} $1_vector_$length'$1_storage_gas_Point'(v: Vec ($1_storage_gas_Point)): int {
    LenVec(v)
}

procedure {:inline 1} $1_vector_borrow'$1_storage_gas_Point'(v: Vec ($1_storage_gas_Point), i: int) returns (dst: $1_storage_gas_Point) {
    if (!InRangeVec(v, i)) {
        call $ExecFailureAbort();
        return;
    }
    dst := ReadVec(v, i);
}

function {:inline} $1_vector_$borrow'$1_storage_gas_Point'(v: Vec ($1_storage_gas_Point), i: int): $1_storage_gas_Point {
    ReadVec(v, i)
}

procedure {:inline 1} $1_vector_borrow_mut'$1_storage_gas_Point'(m: $Mutation (Vec ($1_storage_gas_Point)), index: int)
returns (dst: $Mutation ($1_storage_gas_Point), m': $Mutation (Vec ($1_storage_gas_Point)))
{
    var v: Vec ($1_storage_gas_Point);
    v := $Dereference(m);
    if (!InRangeVec(v, index)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Mutation(l#$Mutation(m), ExtendVec(p#$Mutation(m), index), ReadVec(v, index));
    m' := m;
}

function {:inline} $1_vector_$borrow_mut'$1_storage_gas_Point'(v: Vec ($1_storage_gas_Point), i: int): $1_storage_gas_Point {
    ReadVec(v, i)
}

procedure {:inline 1} $1_vector_destroy_empty'$1_storage_gas_Point'(v: Vec ($1_storage_gas_Point)) {
    if (!IsEmptyVec(v)) {
      call $ExecFailureAbort();
    }
}

procedure {:inline 1} $1_vector_swap'$1_storage_gas_Point'(m: $Mutation (Vec ($1_storage_gas_Point)), i: int, j: int) returns (m': $Mutation (Vec ($1_storage_gas_Point)))
{
    var v: Vec ($1_storage_gas_Point);
    v := $Dereference(m);
    if (!InRangeVec(v, i) || !InRangeVec(v, j)) {
        call $ExecFailureAbort();
        return;
    }
    m' := $UpdateMutation(m, SwapVec(v, i, j));
}

function {:inline} $1_vector_$swap'$1_storage_gas_Point'(v: Vec ($1_storage_gas_Point), i: int, j: int): Vec ($1_storage_gas_Point) {
    SwapVec(v, i, j)
}

procedure {:inline 1} $1_vector_remove'$1_storage_gas_Point'(m: $Mutation (Vec ($1_storage_gas_Point)), i: int) returns (e: $1_storage_gas_Point, m': $Mutation (Vec ($1_storage_gas_Point)))
{
    var v: Vec ($1_storage_gas_Point);

    v := $Dereference(m);

    if (!InRangeVec(v, i)) {
        call $ExecFailureAbort();
        return;
    }
    e := ReadVec(v, i);
    m' := $UpdateMutation(m, RemoveAtVec(v, i));
}

procedure {:inline 1} $1_vector_swap_remove'$1_storage_gas_Point'(m: $Mutation (Vec ($1_storage_gas_Point)), i: int) returns (e: $1_storage_gas_Point, m': $Mutation (Vec ($1_storage_gas_Point)))
{
    var len: int;
    var v: Vec ($1_storage_gas_Point);

    v := $Dereference(m);
    len := LenVec(v);
    if (!InRangeVec(v, i)) {
        call $ExecFailureAbort();
        return;
    }
    e := ReadVec(v, i);
    m' := $UpdateMutation(m, RemoveVec(SwapVec(v, i, len-1)));
}

procedure {:inline 1} $1_vector_contains'$1_storage_gas_Point'(v: Vec ($1_storage_gas_Point), e: $1_storage_gas_Point) returns (res: bool)  {
    res := $ContainsVec'$1_storage_gas_Point'(v, e);
}

procedure {:inline 1}
$1_vector_index_of'$1_storage_gas_Point'(v: Vec ($1_storage_gas_Point), e: $1_storage_gas_Point) returns (res1: bool, res2: int) {
    res2 := $IndexOfVec'$1_storage_gas_Point'(v, e);
    if (res2 >= 0) {
        res1 := true;
    } else {
        res1 := false;
        res2 := 0;
    }
}


// ----------------------------------------------------------------------------------
// Native Vector implementation for element type `u128`

// Not inlined. It appears faster this way.
function $IsEqual'vec'u128''(v1: Vec (int), v2: Vec (int)): bool {
    LenVec(v1) == LenVec(v2) &&
    (forall i: int:: InRangeVec(v1, i) ==> $IsEqual'u128'(ReadVec(v1, i), ReadVec(v2, i)))
}

// Not inlined.
function $IsPrefix'vec'u128''(v: Vec (int), prefix: Vec (int)): bool {
    LenVec(v) >= LenVec(prefix) &&
    (forall i: int:: InRangeVec(prefix, i) ==> $IsEqual'u128'(ReadVec(v, i), ReadVec(prefix, i)))
}

// Not inlined.
function $IsSuffix'vec'u128''(v: Vec (int), suffix: Vec (int)): bool {
    LenVec(v) >= LenVec(suffix) &&
    (forall i: int:: InRangeVec(suffix, i) ==> $IsEqual'u128'(ReadVec(v, LenVec(v) - LenVec(suffix) + i), ReadVec(suffix, i)))
}

// Not inlined.
function $IsValid'vec'u128''(v: Vec (int)): bool {
    $IsValid'u64'(LenVec(v)) &&
    (forall i: int:: InRangeVec(v, i) ==> $IsValid'u128'(ReadVec(v, i)))
}


function {:inline} $ContainsVec'u128'(v: Vec (int), e: int): bool {
    (exists i: int :: $IsValid'u64'(i) && InRangeVec(v, i) && $IsEqual'u128'(ReadVec(v, i), e))
}

function $IndexOfVec'u128'(v: Vec (int), e: int): int;
axiom (forall v: Vec (int), e: int:: {$IndexOfVec'u128'(v, e)}
    (var i := $IndexOfVec'u128'(v, e);
     if (!$ContainsVec'u128'(v, e)) then i == -1
     else $IsValid'u64'(i) && InRangeVec(v, i) && $IsEqual'u128'(ReadVec(v, i), e) &&
        (forall j: int :: $IsValid'u64'(j) && j >= 0 && j < i ==> !$IsEqual'u128'(ReadVec(v, j), e))));


function {:inline} $RangeVec'u128'(v: Vec (int)): $Range {
    $Range(0, LenVec(v))
}


function {:inline} $EmptyVec'u128'(): Vec (int) {
    EmptyVec()
}

procedure {:inline 1} $1_vector_empty'u128'() returns (v: Vec (int)) {
    v := EmptyVec();
}

function {:inline} $1_vector_$empty'u128'(): Vec (int) {
    EmptyVec()
}

procedure {:inline 1} $1_vector_is_empty'u128'(v: Vec (int)) returns (b: bool) {
    b := IsEmptyVec(v);
}

procedure {:inline 1} $1_vector_push_back'u128'(m: $Mutation (Vec (int)), val: int) returns (m': $Mutation (Vec (int))) {
    m' := $UpdateMutation(m, ExtendVec($Dereference(m), val));
}

function {:inline} $1_vector_$push_back'u128'(v: Vec (int), val: int): Vec (int) {
    ExtendVec(v, val)
}

procedure {:inline 1} $1_vector_pop_back'u128'(m: $Mutation (Vec (int))) returns (e: int, m': $Mutation (Vec (int))) {
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

procedure {:inline 1} $1_vector_append'u128'(m: $Mutation (Vec (int)), other: Vec (int)) returns (m': $Mutation (Vec (int))) {
    m' := $UpdateMutation(m, ConcatVec($Dereference(m), other));
}

procedure {:inline 1} $1_vector_reverse'u128'(m: $Mutation (Vec (int))) returns (m': $Mutation (Vec (int))) {
    m' := $UpdateMutation(m, ReverseVec($Dereference(m)));
}

procedure {:inline 1} $1_vector_reverse_append'u128'(m: $Mutation (Vec (int)), other: Vec (int)) returns (m': $Mutation (Vec (int))) {
    m' := $UpdateMutation(m, ConcatVec($Dereference(m), ReverseVec(other)));
}

procedure {:inline 1} $1_vector_trim_reverse'u128'(m: $Mutation (Vec (int)), new_len: int) returns (v: (Vec (int)), m': $Mutation (Vec (int))) {
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

procedure {:inline 1} $1_vector_trim'u128'(m: $Mutation (Vec (int)), new_len: int) returns (v: (Vec (int)), m': $Mutation (Vec (int))) {
    var len: int;
    v := $Dereference(m);
    if (LenVec(v) < new_len) {
        call $ExecFailureAbort();
        return;
    }
    v := SliceVec(v, new_len, LenVec(v));
    m' := $UpdateMutation(m, SliceVec($Dereference(m), 0, new_len));
}

procedure {:inline 1} $1_vector_reverse_slice'u128'(m: $Mutation (Vec (int)), left: int, right: int) returns (m': $Mutation (Vec (int))) {
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

procedure {:inline 1} $1_vector_rotate'u128'(m: $Mutation (Vec (int)), rot: int) returns (n: int, m': $Mutation (Vec (int))) {
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

procedure {:inline 1} $1_vector_rotate_slice'u128'(m: $Mutation (Vec (int)), left: int, rot: int, right: int) returns (n: int, m': $Mutation (Vec (int))) {
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

procedure {:inline 1} $1_vector_insert'u128'(m: $Mutation (Vec (int)), i: int, e: int) returns (m': $Mutation (Vec (int))) {
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

procedure {:inline 1} $1_vector_length'u128'(v: Vec (int)) returns (l: int) {
    l := LenVec(v);
}

function {:inline} $1_vector_$length'u128'(v: Vec (int)): int {
    LenVec(v)
}

procedure {:inline 1} $1_vector_borrow'u128'(v: Vec (int), i: int) returns (dst: int) {
    if (!InRangeVec(v, i)) {
        call $ExecFailureAbort();
        return;
    }
    dst := ReadVec(v, i);
}

function {:inline} $1_vector_$borrow'u128'(v: Vec (int), i: int): int {
    ReadVec(v, i)
}

procedure {:inline 1} $1_vector_borrow_mut'u128'(m: $Mutation (Vec (int)), index: int)
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

function {:inline} $1_vector_$borrow_mut'u128'(v: Vec (int), i: int): int {
    ReadVec(v, i)
}

procedure {:inline 1} $1_vector_destroy_empty'u128'(v: Vec (int)) {
    if (!IsEmptyVec(v)) {
      call $ExecFailureAbort();
    }
}

procedure {:inline 1} $1_vector_swap'u128'(m: $Mutation (Vec (int)), i: int, j: int) returns (m': $Mutation (Vec (int)))
{
    var v: Vec (int);
    v := $Dereference(m);
    if (!InRangeVec(v, i) || !InRangeVec(v, j)) {
        call $ExecFailureAbort();
        return;
    }
    m' := $UpdateMutation(m, SwapVec(v, i, j));
}

function {:inline} $1_vector_$swap'u128'(v: Vec (int), i: int, j: int): Vec (int) {
    SwapVec(v, i, j)
}

procedure {:inline 1} $1_vector_remove'u128'(m: $Mutation (Vec (int)), i: int) returns (e: int, m': $Mutation (Vec (int)))
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

procedure {:inline 1} $1_vector_swap_remove'u128'(m: $Mutation (Vec (int)), i: int) returns (e: int, m': $Mutation (Vec (int)))
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

procedure {:inline 1} $1_vector_contains'u128'(v: Vec (int), e: int) returns (res: bool)  {
    res := $ContainsVec'u128'(v, e);
}

procedure {:inline 1}
$1_vector_index_of'u128'(v: Vec (int), e: int) returns (res1: bool, res2: int) {
    res2 := $IndexOfVec'u128'(v, e);
    if (res2 >= 0) {
        res1 := true;
    } else {
        res1 := false;
        res2 := 0;
    }
}


// ----------------------------------------------------------------------------------
// Native Vector implementation for element type `u64`

// Not inlined. It appears faster this way.
function $IsEqual'vec'u64''(v1: Vec (int), v2: Vec (int)): bool {
    LenVec(v1) == LenVec(v2) &&
    (forall i: int:: InRangeVec(v1, i) ==> $IsEqual'u64'(ReadVec(v1, i), ReadVec(v2, i)))
}

// Not inlined.
function $IsPrefix'vec'u64''(v: Vec (int), prefix: Vec (int)): bool {
    LenVec(v) >= LenVec(prefix) &&
    (forall i: int:: InRangeVec(prefix, i) ==> $IsEqual'u64'(ReadVec(v, i), ReadVec(prefix, i)))
}

// Not inlined.
function $IsSuffix'vec'u64''(v: Vec (int), suffix: Vec (int)): bool {
    LenVec(v) >= LenVec(suffix) &&
    (forall i: int:: InRangeVec(suffix, i) ==> $IsEqual'u64'(ReadVec(v, LenVec(v) - LenVec(suffix) + i), ReadVec(suffix, i)))
}

// Not inlined.
function $IsValid'vec'u64''(v: Vec (int)): bool {
    $IsValid'u64'(LenVec(v)) &&
    (forall i: int:: InRangeVec(v, i) ==> $IsValid'u64'(ReadVec(v, i)))
}


function {:inline} $ContainsVec'u64'(v: Vec (int), e: int): bool {
    (exists i: int :: $IsValid'u64'(i) && InRangeVec(v, i) && $IsEqual'u64'(ReadVec(v, i), e))
}

function $IndexOfVec'u64'(v: Vec (int), e: int): int;
axiom (forall v: Vec (int), e: int:: {$IndexOfVec'u64'(v, e)}
    (var i := $IndexOfVec'u64'(v, e);
     if (!$ContainsVec'u64'(v, e)) then i == -1
     else $IsValid'u64'(i) && InRangeVec(v, i) && $IsEqual'u64'(ReadVec(v, i), e) &&
        (forall j: int :: $IsValid'u64'(j) && j >= 0 && j < i ==> !$IsEqual'u64'(ReadVec(v, j), e))));


function {:inline} $RangeVec'u64'(v: Vec (int)): $Range {
    $Range(0, LenVec(v))
}


function {:inline} $EmptyVec'u64'(): Vec (int) {
    EmptyVec()
}

procedure {:inline 1} $1_vector_empty'u64'() returns (v: Vec (int)) {
    v := EmptyVec();
}

function {:inline} $1_vector_$empty'u64'(): Vec (int) {
    EmptyVec()
}

procedure {:inline 1} $1_vector_is_empty'u64'(v: Vec (int)) returns (b: bool) {
    b := IsEmptyVec(v);
}

procedure {:inline 1} $1_vector_push_back'u64'(m: $Mutation (Vec (int)), val: int) returns (m': $Mutation (Vec (int))) {
    m' := $UpdateMutation(m, ExtendVec($Dereference(m), val));
}

function {:inline} $1_vector_$push_back'u64'(v: Vec (int), val: int): Vec (int) {
    ExtendVec(v, val)
}

procedure {:inline 1} $1_vector_pop_back'u64'(m: $Mutation (Vec (int))) returns (e: int, m': $Mutation (Vec (int))) {
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

procedure {:inline 1} $1_vector_append'u64'(m: $Mutation (Vec (int)), other: Vec (int)) returns (m': $Mutation (Vec (int))) {
    m' := $UpdateMutation(m, ConcatVec($Dereference(m), other));
}

procedure {:inline 1} $1_vector_reverse'u64'(m: $Mutation (Vec (int))) returns (m': $Mutation (Vec (int))) {
    m' := $UpdateMutation(m, ReverseVec($Dereference(m)));
}

procedure {:inline 1} $1_vector_reverse_append'u64'(m: $Mutation (Vec (int)), other: Vec (int)) returns (m': $Mutation (Vec (int))) {
    m' := $UpdateMutation(m, ConcatVec($Dereference(m), ReverseVec(other)));
}

procedure {:inline 1} $1_vector_trim_reverse'u64'(m: $Mutation (Vec (int)), new_len: int) returns (v: (Vec (int)), m': $Mutation (Vec (int))) {
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

procedure {:inline 1} $1_vector_trim'u64'(m: $Mutation (Vec (int)), new_len: int) returns (v: (Vec (int)), m': $Mutation (Vec (int))) {
    var len: int;
    v := $Dereference(m);
    if (LenVec(v) < new_len) {
        call $ExecFailureAbort();
        return;
    }
    v := SliceVec(v, new_len, LenVec(v));
    m' := $UpdateMutation(m, SliceVec($Dereference(m), 0, new_len));
}

procedure {:inline 1} $1_vector_reverse_slice'u64'(m: $Mutation (Vec (int)), left: int, right: int) returns (m': $Mutation (Vec (int))) {
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

procedure {:inline 1} $1_vector_rotate'u64'(m: $Mutation (Vec (int)), rot: int) returns (n: int, m': $Mutation (Vec (int))) {
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

procedure {:inline 1} $1_vector_rotate_slice'u64'(m: $Mutation (Vec (int)), left: int, rot: int, right: int) returns (n: int, m': $Mutation (Vec (int))) {
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

procedure {:inline 1} $1_vector_insert'u64'(m: $Mutation (Vec (int)), i: int, e: int) returns (m': $Mutation (Vec (int))) {
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

procedure {:inline 1} $1_vector_length'u64'(v: Vec (int)) returns (l: int) {
    l := LenVec(v);
}

function {:inline} $1_vector_$length'u64'(v: Vec (int)): int {
    LenVec(v)
}

procedure {:inline 1} $1_vector_borrow'u64'(v: Vec (int), i: int) returns (dst: int) {
    if (!InRangeVec(v, i)) {
        call $ExecFailureAbort();
        return;
    }
    dst := ReadVec(v, i);
}

function {:inline} $1_vector_$borrow'u64'(v: Vec (int), i: int): int {
    ReadVec(v, i)
}

procedure {:inline 1} $1_vector_borrow_mut'u64'(m: $Mutation (Vec (int)), index: int)
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

function {:inline} $1_vector_$borrow_mut'u64'(v: Vec (int), i: int): int {
    ReadVec(v, i)
}

procedure {:inline 1} $1_vector_destroy_empty'u64'(v: Vec (int)) {
    if (!IsEmptyVec(v)) {
      call $ExecFailureAbort();
    }
}

procedure {:inline 1} $1_vector_swap'u64'(m: $Mutation (Vec (int)), i: int, j: int) returns (m': $Mutation (Vec (int)))
{
    var v: Vec (int);
    v := $Dereference(m);
    if (!InRangeVec(v, i) || !InRangeVec(v, j)) {
        call $ExecFailureAbort();
        return;
    }
    m' := $UpdateMutation(m, SwapVec(v, i, j));
}

function {:inline} $1_vector_$swap'u64'(v: Vec (int), i: int, j: int): Vec (int) {
    SwapVec(v, i, j)
}

procedure {:inline 1} $1_vector_remove'u64'(m: $Mutation (Vec (int)), i: int) returns (e: int, m': $Mutation (Vec (int)))
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

procedure {:inline 1} $1_vector_swap_remove'u64'(m: $Mutation (Vec (int)), i: int) returns (e: int, m': $Mutation (Vec (int)))
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

procedure {:inline 1} $1_vector_contains'u64'(v: Vec (int), e: int) returns (res: bool)  {
    res := $ContainsVec'u64'(v, e);
}

procedure {:inline 1}
$1_vector_index_of'u64'(v: Vec (int), e: int) returns (res1: bool, res2: int) {
    res2 := $IndexOfVec'u64'(v, e);
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
// Native Vector implementation for element type `bv128`

// Not inlined. It appears faster this way.
function $IsEqual'vec'bv128''(v1: Vec (bv128), v2: Vec (bv128)): bool {
    LenVec(v1) == LenVec(v2) &&
    (forall i: int:: InRangeVec(v1, i) ==> $IsEqual'bv128'(ReadVec(v1, i), ReadVec(v2, i)))
}

// Not inlined.
function $IsPrefix'vec'bv128''(v: Vec (bv128), prefix: Vec (bv128)): bool {
    LenVec(v) >= LenVec(prefix) &&
    (forall i: int:: InRangeVec(prefix, i) ==> $IsEqual'bv128'(ReadVec(v, i), ReadVec(prefix, i)))
}

// Not inlined.
function $IsSuffix'vec'bv128''(v: Vec (bv128), suffix: Vec (bv128)): bool {
    LenVec(v) >= LenVec(suffix) &&
    (forall i: int:: InRangeVec(suffix, i) ==> $IsEqual'bv128'(ReadVec(v, LenVec(v) - LenVec(suffix) + i), ReadVec(suffix, i)))
}

// Not inlined.
function $IsValid'vec'bv128''(v: Vec (bv128)): bool {
    $IsValid'u64'(LenVec(v)) &&
    (forall i: int:: InRangeVec(v, i) ==> $IsValid'bv128'(ReadVec(v, i)))
}


function {:inline} $ContainsVec'bv128'(v: Vec (bv128), e: bv128): bool {
    (exists i: int :: $IsValid'u64'(i) && InRangeVec(v, i) && $IsEqual'bv128'(ReadVec(v, i), e))
}

function $IndexOfVec'bv128'(v: Vec (bv128), e: bv128): int;
axiom (forall v: Vec (bv128), e: bv128:: {$IndexOfVec'bv128'(v, e)}
    (var i := $IndexOfVec'bv128'(v, e);
     if (!$ContainsVec'bv128'(v, e)) then i == -1
     else $IsValid'u64'(i) && InRangeVec(v, i) && $IsEqual'bv128'(ReadVec(v, i), e) &&
        (forall j: int :: $IsValid'u64'(j) && j >= 0 && j < i ==> !$IsEqual'bv128'(ReadVec(v, j), e))));


function {:inline} $RangeVec'bv128'(v: Vec (bv128)): $Range {
    $Range(0, LenVec(v))
}


function {:inline} $EmptyVec'bv128'(): Vec (bv128) {
    EmptyVec()
}

procedure {:inline 1} $1_vector_empty'bv128'() returns (v: Vec (bv128)) {
    v := EmptyVec();
}

function {:inline} $1_vector_$empty'bv128'(): Vec (bv128) {
    EmptyVec()
}

procedure {:inline 1} $1_vector_is_empty'bv128'(v: Vec (bv128)) returns (b: bool) {
    b := IsEmptyVec(v);
}

procedure {:inline 1} $1_vector_push_back'bv128'(m: $Mutation (Vec (bv128)), val: bv128) returns (m': $Mutation (Vec (bv128))) {
    m' := $UpdateMutation(m, ExtendVec($Dereference(m), val));
}

function {:inline} $1_vector_$push_back'bv128'(v: Vec (bv128), val: bv128): Vec (bv128) {
    ExtendVec(v, val)
}

procedure {:inline 1} $1_vector_pop_back'bv128'(m: $Mutation (Vec (bv128))) returns (e: bv128, m': $Mutation (Vec (bv128))) {
    var v: Vec (bv128);
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

procedure {:inline 1} $1_vector_append'bv128'(m: $Mutation (Vec (bv128)), other: Vec (bv128)) returns (m': $Mutation (Vec (bv128))) {
    m' := $UpdateMutation(m, ConcatVec($Dereference(m), other));
}

procedure {:inline 1} $1_vector_reverse'bv128'(m: $Mutation (Vec (bv128))) returns (m': $Mutation (Vec (bv128))) {
    m' := $UpdateMutation(m, ReverseVec($Dereference(m)));
}

procedure {:inline 1} $1_vector_reverse_append'bv128'(m: $Mutation (Vec (bv128)), other: Vec (bv128)) returns (m': $Mutation (Vec (bv128))) {
    m' := $UpdateMutation(m, ConcatVec($Dereference(m), ReverseVec(other)));
}

procedure {:inline 1} $1_vector_trim_reverse'bv128'(m: $Mutation (Vec (bv128)), new_len: int) returns (v: (Vec (bv128)), m': $Mutation (Vec (bv128))) {
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

procedure {:inline 1} $1_vector_trim'bv128'(m: $Mutation (Vec (bv128)), new_len: int) returns (v: (Vec (bv128)), m': $Mutation (Vec (bv128))) {
    var len: int;
    v := $Dereference(m);
    if (LenVec(v) < new_len) {
        call $ExecFailureAbort();
        return;
    }
    v := SliceVec(v, new_len, LenVec(v));
    m' := $UpdateMutation(m, SliceVec($Dereference(m), 0, new_len));
}

procedure {:inline 1} $1_vector_reverse_slice'bv128'(m: $Mutation (Vec (bv128)), left: int, right: int) returns (m': $Mutation (Vec (bv128))) {
    var left_vec: Vec (bv128);
    var mid_vec: Vec (bv128);
    var right_vec: Vec (bv128);
    var v: Vec (bv128);
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

procedure {:inline 1} $1_vector_rotate'bv128'(m: $Mutation (Vec (bv128)), rot: int) returns (n: int, m': $Mutation (Vec (bv128))) {
    var v: Vec (bv128);
    var len: int;
    var left_vec: Vec (bv128);
    var right_vec: Vec (bv128);
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

procedure {:inline 1} $1_vector_rotate_slice'bv128'(m: $Mutation (Vec (bv128)), left: int, rot: int, right: int) returns (n: int, m': $Mutation (Vec (bv128))) {
    var left_vec: Vec (bv128);
    var mid_vec: Vec (bv128);
    var right_vec: Vec (bv128);
    var mid_left_vec: Vec (bv128);
    var mid_right_vec: Vec (bv128);
    var v: Vec (bv128);
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

procedure {:inline 1} $1_vector_insert'bv128'(m: $Mutation (Vec (bv128)), i: int, e: bv128) returns (m': $Mutation (Vec (bv128))) {
    var left_vec: Vec (bv128);
    var right_vec: Vec (bv128);
    var v: Vec (bv128);
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

procedure {:inline 1} $1_vector_length'bv128'(v: Vec (bv128)) returns (l: int) {
    l := LenVec(v);
}

function {:inline} $1_vector_$length'bv128'(v: Vec (bv128)): int {
    LenVec(v)
}

procedure {:inline 1} $1_vector_borrow'bv128'(v: Vec (bv128), i: int) returns (dst: bv128) {
    if (!InRangeVec(v, i)) {
        call $ExecFailureAbort();
        return;
    }
    dst := ReadVec(v, i);
}

function {:inline} $1_vector_$borrow'bv128'(v: Vec (bv128), i: int): bv128 {
    ReadVec(v, i)
}

procedure {:inline 1} $1_vector_borrow_mut'bv128'(m: $Mutation (Vec (bv128)), index: int)
returns (dst: $Mutation (bv128), m': $Mutation (Vec (bv128)))
{
    var v: Vec (bv128);
    v := $Dereference(m);
    if (!InRangeVec(v, index)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Mutation(l#$Mutation(m), ExtendVec(p#$Mutation(m), index), ReadVec(v, index));
    m' := m;
}

function {:inline} $1_vector_$borrow_mut'bv128'(v: Vec (bv128), i: int): bv128 {
    ReadVec(v, i)
}

procedure {:inline 1} $1_vector_destroy_empty'bv128'(v: Vec (bv128)) {
    if (!IsEmptyVec(v)) {
      call $ExecFailureAbort();
    }
}

procedure {:inline 1} $1_vector_swap'bv128'(m: $Mutation (Vec (bv128)), i: int, j: int) returns (m': $Mutation (Vec (bv128)))
{
    var v: Vec (bv128);
    v := $Dereference(m);
    if (!InRangeVec(v, i) || !InRangeVec(v, j)) {
        call $ExecFailureAbort();
        return;
    }
    m' := $UpdateMutation(m, SwapVec(v, i, j));
}

function {:inline} $1_vector_$swap'bv128'(v: Vec (bv128), i: int, j: int): Vec (bv128) {
    SwapVec(v, i, j)
}

procedure {:inline 1} $1_vector_remove'bv128'(m: $Mutation (Vec (bv128)), i: int) returns (e: bv128, m': $Mutation (Vec (bv128)))
{
    var v: Vec (bv128);

    v := $Dereference(m);

    if (!InRangeVec(v, i)) {
        call $ExecFailureAbort();
        return;
    }
    e := ReadVec(v, i);
    m' := $UpdateMutation(m, RemoveAtVec(v, i));
}

procedure {:inline 1} $1_vector_swap_remove'bv128'(m: $Mutation (Vec (bv128)), i: int) returns (e: bv128, m': $Mutation (Vec (bv128)))
{
    var len: int;
    var v: Vec (bv128);

    v := $Dereference(m);
    len := LenVec(v);
    if (!InRangeVec(v, i)) {
        call $ExecFailureAbort();
        return;
    }
    e := ReadVec(v, i);
    m' := $UpdateMutation(m, RemoveVec(SwapVec(v, i, len-1)));
}

procedure {:inline 1} $1_vector_contains'bv128'(v: Vec (bv128), e: bv128) returns (res: bool)  {
    res := $ContainsVec'bv128'(v, e);
}

procedure {:inline 1}
$1_vector_index_of'bv128'(v: Vec (bv128), e: bv128) returns (res1: bool, res2: int) {
    res2 := $IndexOfVec'bv128'(v, e);
    if (res2 >= 0) {
        res1 := true;
    } else {
        res1 := false;
        res2 := 0;
    }
}


// ----------------------------------------------------------------------------------
// Native Vector implementation for element type `bv64`

// Not inlined. It appears faster this way.
function $IsEqual'vec'bv64''(v1: Vec (bv64), v2: Vec (bv64)): bool {
    LenVec(v1) == LenVec(v2) &&
    (forall i: int:: InRangeVec(v1, i) ==> $IsEqual'bv64'(ReadVec(v1, i), ReadVec(v2, i)))
}

// Not inlined.
function $IsPrefix'vec'bv64''(v: Vec (bv64), prefix: Vec (bv64)): bool {
    LenVec(v) >= LenVec(prefix) &&
    (forall i: int:: InRangeVec(prefix, i) ==> $IsEqual'bv64'(ReadVec(v, i), ReadVec(prefix, i)))
}

// Not inlined.
function $IsSuffix'vec'bv64''(v: Vec (bv64), suffix: Vec (bv64)): bool {
    LenVec(v) >= LenVec(suffix) &&
    (forall i: int:: InRangeVec(suffix, i) ==> $IsEqual'bv64'(ReadVec(v, LenVec(v) - LenVec(suffix) + i), ReadVec(suffix, i)))
}

// Not inlined.
function $IsValid'vec'bv64''(v: Vec (bv64)): bool {
    $IsValid'u64'(LenVec(v)) &&
    (forall i: int:: InRangeVec(v, i) ==> $IsValid'bv64'(ReadVec(v, i)))
}


function {:inline} $ContainsVec'bv64'(v: Vec (bv64), e: bv64): bool {
    (exists i: int :: $IsValid'u64'(i) && InRangeVec(v, i) && $IsEqual'bv64'(ReadVec(v, i), e))
}

function $IndexOfVec'bv64'(v: Vec (bv64), e: bv64): int;
axiom (forall v: Vec (bv64), e: bv64:: {$IndexOfVec'bv64'(v, e)}
    (var i := $IndexOfVec'bv64'(v, e);
     if (!$ContainsVec'bv64'(v, e)) then i == -1
     else $IsValid'u64'(i) && InRangeVec(v, i) && $IsEqual'bv64'(ReadVec(v, i), e) &&
        (forall j: int :: $IsValid'u64'(j) && j >= 0 && j < i ==> !$IsEqual'bv64'(ReadVec(v, j), e))));


function {:inline} $RangeVec'bv64'(v: Vec (bv64)): $Range {
    $Range(0, LenVec(v))
}


function {:inline} $EmptyVec'bv64'(): Vec (bv64) {
    EmptyVec()
}

procedure {:inline 1} $1_vector_empty'bv64'() returns (v: Vec (bv64)) {
    v := EmptyVec();
}

function {:inline} $1_vector_$empty'bv64'(): Vec (bv64) {
    EmptyVec()
}

procedure {:inline 1} $1_vector_is_empty'bv64'(v: Vec (bv64)) returns (b: bool) {
    b := IsEmptyVec(v);
}

procedure {:inline 1} $1_vector_push_back'bv64'(m: $Mutation (Vec (bv64)), val: bv64) returns (m': $Mutation (Vec (bv64))) {
    m' := $UpdateMutation(m, ExtendVec($Dereference(m), val));
}

function {:inline} $1_vector_$push_back'bv64'(v: Vec (bv64), val: bv64): Vec (bv64) {
    ExtendVec(v, val)
}

procedure {:inline 1} $1_vector_pop_back'bv64'(m: $Mutation (Vec (bv64))) returns (e: bv64, m': $Mutation (Vec (bv64))) {
    var v: Vec (bv64);
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

procedure {:inline 1} $1_vector_append'bv64'(m: $Mutation (Vec (bv64)), other: Vec (bv64)) returns (m': $Mutation (Vec (bv64))) {
    m' := $UpdateMutation(m, ConcatVec($Dereference(m), other));
}

procedure {:inline 1} $1_vector_reverse'bv64'(m: $Mutation (Vec (bv64))) returns (m': $Mutation (Vec (bv64))) {
    m' := $UpdateMutation(m, ReverseVec($Dereference(m)));
}

procedure {:inline 1} $1_vector_reverse_append'bv64'(m: $Mutation (Vec (bv64)), other: Vec (bv64)) returns (m': $Mutation (Vec (bv64))) {
    m' := $UpdateMutation(m, ConcatVec($Dereference(m), ReverseVec(other)));
}

procedure {:inline 1} $1_vector_trim_reverse'bv64'(m: $Mutation (Vec (bv64)), new_len: int) returns (v: (Vec (bv64)), m': $Mutation (Vec (bv64))) {
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

procedure {:inline 1} $1_vector_trim'bv64'(m: $Mutation (Vec (bv64)), new_len: int) returns (v: (Vec (bv64)), m': $Mutation (Vec (bv64))) {
    var len: int;
    v := $Dereference(m);
    if (LenVec(v) < new_len) {
        call $ExecFailureAbort();
        return;
    }
    v := SliceVec(v, new_len, LenVec(v));
    m' := $UpdateMutation(m, SliceVec($Dereference(m), 0, new_len));
}

procedure {:inline 1} $1_vector_reverse_slice'bv64'(m: $Mutation (Vec (bv64)), left: int, right: int) returns (m': $Mutation (Vec (bv64))) {
    var left_vec: Vec (bv64);
    var mid_vec: Vec (bv64);
    var right_vec: Vec (bv64);
    var v: Vec (bv64);
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

procedure {:inline 1} $1_vector_rotate'bv64'(m: $Mutation (Vec (bv64)), rot: int) returns (n: int, m': $Mutation (Vec (bv64))) {
    var v: Vec (bv64);
    var len: int;
    var left_vec: Vec (bv64);
    var right_vec: Vec (bv64);
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

procedure {:inline 1} $1_vector_rotate_slice'bv64'(m: $Mutation (Vec (bv64)), left: int, rot: int, right: int) returns (n: int, m': $Mutation (Vec (bv64))) {
    var left_vec: Vec (bv64);
    var mid_vec: Vec (bv64);
    var right_vec: Vec (bv64);
    var mid_left_vec: Vec (bv64);
    var mid_right_vec: Vec (bv64);
    var v: Vec (bv64);
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

procedure {:inline 1} $1_vector_insert'bv64'(m: $Mutation (Vec (bv64)), i: int, e: bv64) returns (m': $Mutation (Vec (bv64))) {
    var left_vec: Vec (bv64);
    var right_vec: Vec (bv64);
    var v: Vec (bv64);
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

procedure {:inline 1} $1_vector_length'bv64'(v: Vec (bv64)) returns (l: int) {
    l := LenVec(v);
}

function {:inline} $1_vector_$length'bv64'(v: Vec (bv64)): int {
    LenVec(v)
}

procedure {:inline 1} $1_vector_borrow'bv64'(v: Vec (bv64), i: int) returns (dst: bv64) {
    if (!InRangeVec(v, i)) {
        call $ExecFailureAbort();
        return;
    }
    dst := ReadVec(v, i);
}

function {:inline} $1_vector_$borrow'bv64'(v: Vec (bv64), i: int): bv64 {
    ReadVec(v, i)
}

procedure {:inline 1} $1_vector_borrow_mut'bv64'(m: $Mutation (Vec (bv64)), index: int)
returns (dst: $Mutation (bv64), m': $Mutation (Vec (bv64)))
{
    var v: Vec (bv64);
    v := $Dereference(m);
    if (!InRangeVec(v, index)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Mutation(l#$Mutation(m), ExtendVec(p#$Mutation(m), index), ReadVec(v, index));
    m' := m;
}

function {:inline} $1_vector_$borrow_mut'bv64'(v: Vec (bv64), i: int): bv64 {
    ReadVec(v, i)
}

procedure {:inline 1} $1_vector_destroy_empty'bv64'(v: Vec (bv64)) {
    if (!IsEmptyVec(v)) {
      call $ExecFailureAbort();
    }
}

procedure {:inline 1} $1_vector_swap'bv64'(m: $Mutation (Vec (bv64)), i: int, j: int) returns (m': $Mutation (Vec (bv64)))
{
    var v: Vec (bv64);
    v := $Dereference(m);
    if (!InRangeVec(v, i) || !InRangeVec(v, j)) {
        call $ExecFailureAbort();
        return;
    }
    m' := $UpdateMutation(m, SwapVec(v, i, j));
}

function {:inline} $1_vector_$swap'bv64'(v: Vec (bv64), i: int, j: int): Vec (bv64) {
    SwapVec(v, i, j)
}

procedure {:inline 1} $1_vector_remove'bv64'(m: $Mutation (Vec (bv64)), i: int) returns (e: bv64, m': $Mutation (Vec (bv64)))
{
    var v: Vec (bv64);

    v := $Dereference(m);

    if (!InRangeVec(v, i)) {
        call $ExecFailureAbort();
        return;
    }
    e := ReadVec(v, i);
    m' := $UpdateMutation(m, RemoveAtVec(v, i));
}

procedure {:inline 1} $1_vector_swap_remove'bv64'(m: $Mutation (Vec (bv64)), i: int) returns (e: bv64, m': $Mutation (Vec (bv64)))
{
    var len: int;
    var v: Vec (bv64);

    v := $Dereference(m);
    len := LenVec(v);
    if (!InRangeVec(v, i)) {
        call $ExecFailureAbort();
        return;
    }
    e := ReadVec(v, i);
    m' := $UpdateMutation(m, RemoveVec(SwapVec(v, i, len-1)));
}

procedure {:inline 1} $1_vector_contains'bv64'(v: Vec (bv64), e: bv64) returns (res: bool)  {
    res := $ContainsVec'bv64'(v, e);
}

procedure {:inline 1}
$1_vector_index_of'bv64'(v: Vec (bv64), e: bv64) returns (res1: bool, res2: int) {
    res2 := $IndexOfVec'bv64'(v, e);
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
// Native Table key encoding for type `u64`

function $EncodeKey'u64'(k: int): int;
axiom (
  forall k1, k2: int :: {$EncodeKey'u64'(k1), $EncodeKey'u64'(k2)}
    $IsEqual'u64'(k1, k2) <==> $EncodeKey'u64'(k1) == $EncodeKey'u64'(k2)
);


// ----------------------------------------------------------------------------------
// Native Table key encoding for type `address`

function $EncodeKey'address'(k: int): int;
axiom (
  forall k1, k2: int :: {$EncodeKey'address'(k1), $EncodeKey'address'(k2)}
    $IsEqual'address'(k1, k2) <==> $EncodeKey'address'(k1) == $EncodeKey'address'(k2)
);


// ----------------------------------------------------------------------------------
// Native Table key encoding for type `$1_string_String`

function $EncodeKey'$1_string_String'(k: $1_string_String): int;
axiom (
  forall k1, k2: $1_string_String :: {$EncodeKey'$1_string_String'(k1), $EncodeKey'$1_string_String'(k2)}
    $IsEqual'$1_string_String'(k1, k2) <==> $EncodeKey'$1_string_String'(k1) == $EncodeKey'$1_string_String'(k2)
);


// ----------------------------------------------------------------------------------
// Native Table implementation for type `(u64,$1_voting_Proposal'$1_governance_proposal_GovernanceProposal')`

function $IsEqual'$1_table_Table'u64_$1_voting_Proposal'$1_governance_proposal_GovernanceProposal'''(t1: Table int ($1_voting_Proposal'$1_governance_proposal_GovernanceProposal'), t2: Table int ($1_voting_Proposal'$1_governance_proposal_GovernanceProposal')): bool {
    LenTable(t1) == LenTable(t2) &&
    (forall k: int :: ContainsTable(t1, k) <==> ContainsTable(t2, k)) &&
    (forall k: int :: ContainsTable(t1, k) ==> GetTable(t1, k) == GetTable(t2, k)) &&
    (forall k: int :: ContainsTable(t2, k) ==> GetTable(t1, k) == GetTable(t2, k))
}

// Not inlined.
function $IsValid'$1_table_Table'u64_$1_voting_Proposal'$1_governance_proposal_GovernanceProposal'''(t: Table int ($1_voting_Proposal'$1_governance_proposal_GovernanceProposal')): bool {
    $IsValid'u64'(LenTable(t)) &&
    (forall i: int:: ContainsTable(t, i) ==> $IsValid'$1_voting_Proposal'$1_governance_proposal_GovernanceProposal''(GetTable(t, i)))
}
procedure {:inline 2} $1_table_new'u64_$1_voting_Proposal'$1_governance_proposal_GovernanceProposal''() returns (v: Table int ($1_voting_Proposal'$1_governance_proposal_GovernanceProposal')) {
    v := EmptyTable();
}
procedure {:inline 2} $1_table_destroy'u64_$1_voting_Proposal'$1_governance_proposal_GovernanceProposal''(t: Table int ($1_voting_Proposal'$1_governance_proposal_GovernanceProposal')) {
    if (LenTable(t) != 0) {
        call $Abort($StdError(1/*INVALID_STATE*/, 102/*ENOT_EMPTY*/));
    }
}
procedure {:inline 2} $1_table_contains'u64_$1_voting_Proposal'$1_governance_proposal_GovernanceProposal''(t: (Table int ($1_voting_Proposal'$1_governance_proposal_GovernanceProposal')), k: int) returns (r: bool) {
    r := ContainsTable(t, $EncodeKey'u64'(k));
}
procedure {:inline 2} $1_table_add'u64_$1_voting_Proposal'$1_governance_proposal_GovernanceProposal''(m: $Mutation (Table int ($1_voting_Proposal'$1_governance_proposal_GovernanceProposal')), k: int, v: $1_voting_Proposal'$1_governance_proposal_GovernanceProposal') returns (m': $Mutation(Table int ($1_voting_Proposal'$1_governance_proposal_GovernanceProposal'))) {
    var enc_k: int;
    var t: Table int ($1_voting_Proposal'$1_governance_proposal_GovernanceProposal');
    enc_k := $EncodeKey'u64'(k);
    t := $Dereference(m);
    if (ContainsTable(t, enc_k)) {
        call $Abort($StdError(7/*INVALID_ARGUMENTS*/, 100/*EALREADY_EXISTS*/));
    } else {
        m' := $UpdateMutation(m, AddTable(t, enc_k, v));
    }
}
procedure {:inline 2} $1_table_upsert'u64_$1_voting_Proposal'$1_governance_proposal_GovernanceProposal''(m: $Mutation (Table int ($1_voting_Proposal'$1_governance_proposal_GovernanceProposal')), k: int, v: $1_voting_Proposal'$1_governance_proposal_GovernanceProposal') returns (m': $Mutation(Table int ($1_voting_Proposal'$1_governance_proposal_GovernanceProposal'))) {
    var enc_k: int;
    var t: Table int ($1_voting_Proposal'$1_governance_proposal_GovernanceProposal');
    enc_k := $EncodeKey'u64'(k);
    t := $Dereference(m);
    if (ContainsTable(t, enc_k)) {
        m' := $UpdateMutation(m, UpdateTable(t, enc_k, v));
    } else {
        m' := $UpdateMutation(m, AddTable(t, enc_k, v));
    }
}
procedure {:inline 2} $1_table_remove'u64_$1_voting_Proposal'$1_governance_proposal_GovernanceProposal''(m: $Mutation (Table int ($1_voting_Proposal'$1_governance_proposal_GovernanceProposal')), k: int)
returns (v: $1_voting_Proposal'$1_governance_proposal_GovernanceProposal', m': $Mutation(Table int ($1_voting_Proposal'$1_governance_proposal_GovernanceProposal'))) {
    var enc_k: int;
    var t: Table int ($1_voting_Proposal'$1_governance_proposal_GovernanceProposal');
    enc_k := $EncodeKey'u64'(k);
    t := $Dereference(m);
    if (!ContainsTable(t, enc_k)) {
        call $Abort($StdError(7/*INVALID_ARGUMENTS*/, 101/*ENOT_FOUND*/));
    } else {
        v := GetTable(t, enc_k);
        m' := $UpdateMutation(m, RemoveTable(t, enc_k));
    }
}
procedure {:inline 2} $1_table_borrow'u64_$1_voting_Proposal'$1_governance_proposal_GovernanceProposal''(t: Table int ($1_voting_Proposal'$1_governance_proposal_GovernanceProposal'), k: int) returns (v: $1_voting_Proposal'$1_governance_proposal_GovernanceProposal') {
    var enc_k: int;
    enc_k := $EncodeKey'u64'(k);
    if (!ContainsTable(t, enc_k)) {
        call $Abort($StdError(7/*INVALID_ARGUMENTS*/, 101/*ENOT_FOUND*/));
    } else {
        v := GetTable(t, $EncodeKey'u64'(k));
    }
}
procedure {:inline 2} $1_table_borrow_mut'u64_$1_voting_Proposal'$1_governance_proposal_GovernanceProposal''(m: $Mutation (Table int ($1_voting_Proposal'$1_governance_proposal_GovernanceProposal')), k: int)
returns (dst: $Mutation ($1_voting_Proposal'$1_governance_proposal_GovernanceProposal'), m': $Mutation (Table int ($1_voting_Proposal'$1_governance_proposal_GovernanceProposal'))) {
    var enc_k: int;
    var t: Table int ($1_voting_Proposal'$1_governance_proposal_GovernanceProposal');
    enc_k := $EncodeKey'u64'(k);
    t := $Dereference(m);
    if (!ContainsTable(t, enc_k)) {
        call $Abort($StdError(7/*INVALID_ARGUMENTS*/, 101/*ENOT_FOUND*/));
    } else {
        dst := $Mutation(l#$Mutation(m), ExtendVec(p#$Mutation(m), enc_k), GetTable(t, enc_k));
        m' := m;
    }
}
procedure {:inline 2} $1_table_borrow_mut_with_default'u64_$1_voting_Proposal'$1_governance_proposal_GovernanceProposal''(m: $Mutation (Table int ($1_voting_Proposal'$1_governance_proposal_GovernanceProposal')), k: int, default: $1_voting_Proposal'$1_governance_proposal_GovernanceProposal')
returns (dst: $Mutation ($1_voting_Proposal'$1_governance_proposal_GovernanceProposal'), m': $Mutation (Table int ($1_voting_Proposal'$1_governance_proposal_GovernanceProposal'))) {
    var enc_k: int;
    var t: Table int ($1_voting_Proposal'$1_governance_proposal_GovernanceProposal');
    var t': Table int ($1_voting_Proposal'$1_governance_proposal_GovernanceProposal');
    enc_k := $EncodeKey'u64'(k);
    t := $Dereference(m);
    if (!ContainsTable(t, enc_k)) {
        m' := $UpdateMutation(m, AddTable(t, enc_k, default));
        t' := $Dereference(m');
        dst := $Mutation(l#$Mutation(m'), ExtendVec(p#$Mutation(m'), enc_k), GetTable(t', enc_k));
    } else {
        dst := $Mutation(l#$Mutation(m), ExtendVec(p#$Mutation(m), enc_k), GetTable(t, enc_k));
        m' := m;
    }
}
function {:inline} $1_table_spec_contains'u64_$1_voting_Proposal'$1_governance_proposal_GovernanceProposal''(t: (Table int ($1_voting_Proposal'$1_governance_proposal_GovernanceProposal')), k: int): bool {
    ContainsTable(t, $EncodeKey'u64'(k))
}
function {:inline} $1_table_spec_set'u64_$1_voting_Proposal'$1_governance_proposal_GovernanceProposal''(t: Table int ($1_voting_Proposal'$1_governance_proposal_GovernanceProposal'), k: int, v: $1_voting_Proposal'$1_governance_proposal_GovernanceProposal'): Table int ($1_voting_Proposal'$1_governance_proposal_GovernanceProposal') {
    (var enc_k := $EncodeKey'u64'(k);
    if (ContainsTable(t, enc_k)) then
        UpdateTable(t, enc_k, v)
    else
        AddTable(t, enc_k, v))
}
function {:inline} $1_table_spec_remove'u64_$1_voting_Proposal'$1_governance_proposal_GovernanceProposal''(t: Table int ($1_voting_Proposal'$1_governance_proposal_GovernanceProposal'), k: int): Table int ($1_voting_Proposal'$1_governance_proposal_GovernanceProposal') {
    RemoveTable(t, $EncodeKey'u64'(k))
}
function {:inline} $1_table_spec_get'u64_$1_voting_Proposal'$1_governance_proposal_GovernanceProposal''(t: Table int ($1_voting_Proposal'$1_governance_proposal_GovernanceProposal'), k: int): $1_voting_Proposal'$1_governance_proposal_GovernanceProposal' {
    GetTable(t, $EncodeKey'u64'(k))
}



// ----------------------------------------------------------------------------------
// Native Table implementation for type `(u64,vec'u8')`

function $IsEqual'$1_simple_map_SimpleMap'u64_vec'u8'''(t1: Table int (Vec (int)), t2: Table int (Vec (int))): bool {
    LenTable(t1) == LenTable(t2) &&
    (forall k: int :: ContainsTable(t1, k) <==> ContainsTable(t2, k)) &&
    (forall k: int :: ContainsTable(t1, k) ==> GetTable(t1, k) == GetTable(t2, k)) &&
    (forall k: int :: ContainsTable(t2, k) ==> GetTable(t1, k) == GetTable(t2, k))
}

// Not inlined.
function $IsValid'$1_simple_map_SimpleMap'u64_vec'u8'''(t: Table int (Vec (int))): bool {
    $IsValid'u64'(LenTable(t)) &&
    (forall i: int:: ContainsTable(t, i) ==> $IsValid'vec'u8''(GetTable(t, i)))
}
procedure {:inline 2} $1_simple_map_create'u64_vec'u8''() returns (v: Table int (Vec (int))) {
    v := EmptyTable();
}
procedure {:inline 2} $1_simple_map_destroy_empty'u64_vec'u8''(t: Table int (Vec (int))) {
    if (LenTable(t) != 0) {
        call $Abort($StdError(1/*INVALID_STATE*/, 102/*ENOT_EMPTY*/));
    }
}
procedure {:inline 2} $1_simple_map_length'u64_vec'u8''(t: (Table int (Vec (int)))) returns (l: int) {
    l := LenTable(t);
}
procedure {:inline 2} $1_simple_map_contains_key'u64_vec'u8''(t: (Table int (Vec (int))), k: int) returns (r: bool) {
    r := ContainsTable(t, $EncodeKey'u64'(k));
}
procedure {:inline 2} $1_simple_map_add'u64_vec'u8''(m: $Mutation (Table int (Vec (int))), k: int, v: Vec (int)) returns (m': $Mutation(Table int (Vec (int)))) {
    var enc_k: int;
    var t: Table int (Vec (int));
    enc_k := $EncodeKey'u64'(k);
    t := $Dereference(m);
    if (ContainsTable(t, enc_k)) {
        call $Abort($StdError(7/*INVALID_ARGUMENTS*/, 100/*EALREADY_EXISTS*/));
    } else {
        m' := $UpdateMutation(m, AddTable(t, enc_k, v));
    }
}
procedure {:inline 2} $1_simple_map_remove'u64_vec'u8''(m: $Mutation (Table int (Vec (int))), k: int)
returns (k': int, v: Vec (int), m': $Mutation(Table int (Vec (int)))) {
    var enc_k: int;
    var t: Table int (Vec (int));
    enc_k := $EncodeKey'u64'(k);
    t := $Dereference(m);
    if (!ContainsTable(t, enc_k)) {
        call $Abort($StdError(7/*INVALID_ARGUMENTS*/, 101/*ENOT_FOUND*/));
    } else {
        k' := k;
        v := GetTable(t, enc_k);
        m' := $UpdateMutation(m, RemoveTable(t, enc_k));
    }
}
procedure {:inline 2} $1_simple_map_borrow'u64_vec'u8''(t: Table int (Vec (int)), k: int) returns (v: Vec (int)) {
    var enc_k: int;
    enc_k := $EncodeKey'u64'(k);
    if (!ContainsTable(t, enc_k)) {
        call $Abort($StdError(7/*INVALID_ARGUMENTS*/, 101/*ENOT_FOUND*/));
    } else {
        v := GetTable(t, $EncodeKey'u64'(k));
    }
}
procedure {:inline 2} $1_simple_map_borrow_mut'u64_vec'u8''(m: $Mutation (Table int (Vec (int))), k: int)
returns (dst: $Mutation (Vec (int)), m': $Mutation (Table int (Vec (int)))) {
    var enc_k: int;
    var t: Table int (Vec (int));
    enc_k := $EncodeKey'u64'(k);
    t := $Dereference(m);
    if (!ContainsTable(t, enc_k)) {
        call $Abort($StdError(7/*INVALID_ARGUMENTS*/, 101/*ENOT_FOUND*/));
    } else {
        dst := $Mutation(l#$Mutation(m), ExtendVec(p#$Mutation(m), enc_k), GetTable(t, enc_k));
        m' := m;
    }
}
function {:inline} $1_simple_map_spec_len'u64_vec'u8''(t: (Table int (Vec (int)))): int {
    LenTable(t)
}
function {:inline} $1_simple_map_spec_contains_key'u64_vec'u8''(t: (Table int (Vec (int))), k: int): bool {
    ContainsTable(t, $EncodeKey'u64'(k))
}
function {:inline} $1_simple_map_spec_set'u64_vec'u8''(t: Table int (Vec (int)), k: int, v: Vec (int)): Table int (Vec (int)) {
    (var enc_k := $EncodeKey'u64'(k);
    if (ContainsTable(t, enc_k)) then
        UpdateTable(t, enc_k, v)
    else
        AddTable(t, enc_k, v))
}
function {:inline} $1_simple_map_spec_remove'u64_vec'u8''(t: Table int (Vec (int)), k: int): Table int (Vec (int)) {
    RemoveTable(t, $EncodeKey'u64'(k))
}
function {:inline} $1_simple_map_spec_get'u64_vec'u8''(t: Table int (Vec (int)), k: int): Vec (int) {
    GetTable(t, $EncodeKey'u64'(k))
}



// ----------------------------------------------------------------------------------
// Native Table implementation for type `(address,$1_account_SignerCapability)`

function $IsEqual'$1_simple_map_SimpleMap'address_$1_account_SignerCapability''(t1: Table int ($1_account_SignerCapability), t2: Table int ($1_account_SignerCapability)): bool {
    LenTable(t1) == LenTable(t2) &&
    (forall k: int :: ContainsTable(t1, k) <==> ContainsTable(t2, k)) &&
    (forall k: int :: ContainsTable(t1, k) ==> GetTable(t1, k) == GetTable(t2, k)) &&
    (forall k: int :: ContainsTable(t2, k) ==> GetTable(t1, k) == GetTable(t2, k))
}

// Not inlined.
function $IsValid'$1_simple_map_SimpleMap'address_$1_account_SignerCapability''(t: Table int ($1_account_SignerCapability)): bool {
    $IsValid'u64'(LenTable(t)) &&
    (forall i: int:: ContainsTable(t, i) ==> $IsValid'$1_account_SignerCapability'(GetTable(t, i)))
}
procedure {:inline 2} $1_simple_map_create'address_$1_account_SignerCapability'() returns (v: Table int ($1_account_SignerCapability)) {
    v := EmptyTable();
}
procedure {:inline 2} $1_simple_map_destroy_empty'address_$1_account_SignerCapability'(t: Table int ($1_account_SignerCapability)) {
    if (LenTable(t) != 0) {
        call $Abort($StdError(1/*INVALID_STATE*/, 102/*ENOT_EMPTY*/));
    }
}
procedure {:inline 2} $1_simple_map_length'address_$1_account_SignerCapability'(t: (Table int ($1_account_SignerCapability))) returns (l: int) {
    l := LenTable(t);
}
procedure {:inline 2} $1_simple_map_contains_key'address_$1_account_SignerCapability'(t: (Table int ($1_account_SignerCapability)), k: int) returns (r: bool) {
    r := ContainsTable(t, $EncodeKey'address'(k));
}
procedure {:inline 2} $1_simple_map_add'address_$1_account_SignerCapability'(m: $Mutation (Table int ($1_account_SignerCapability)), k: int, v: $1_account_SignerCapability) returns (m': $Mutation(Table int ($1_account_SignerCapability))) {
    var enc_k: int;
    var t: Table int ($1_account_SignerCapability);
    enc_k := $EncodeKey'address'(k);
    t := $Dereference(m);
    if (ContainsTable(t, enc_k)) {
        call $Abort($StdError(7/*INVALID_ARGUMENTS*/, 100/*EALREADY_EXISTS*/));
    } else {
        m' := $UpdateMutation(m, AddTable(t, enc_k, v));
    }
}
procedure {:inline 2} $1_simple_map_remove'address_$1_account_SignerCapability'(m: $Mutation (Table int ($1_account_SignerCapability)), k: int)
returns (k': int, v: $1_account_SignerCapability, m': $Mutation(Table int ($1_account_SignerCapability))) {
    var enc_k: int;
    var t: Table int ($1_account_SignerCapability);
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
procedure {:inline 2} $1_simple_map_borrow'address_$1_account_SignerCapability'(t: Table int ($1_account_SignerCapability), k: int) returns (v: $1_account_SignerCapability) {
    var enc_k: int;
    enc_k := $EncodeKey'address'(k);
    if (!ContainsTable(t, enc_k)) {
        call $Abort($StdError(7/*INVALID_ARGUMENTS*/, 101/*ENOT_FOUND*/));
    } else {
        v := GetTable(t, $EncodeKey'address'(k));
    }
}
procedure {:inline 2} $1_simple_map_borrow_mut'address_$1_account_SignerCapability'(m: $Mutation (Table int ($1_account_SignerCapability)), k: int)
returns (dst: $Mutation ($1_account_SignerCapability), m': $Mutation (Table int ($1_account_SignerCapability))) {
    var enc_k: int;
    var t: Table int ($1_account_SignerCapability);
    enc_k := $EncodeKey'address'(k);
    t := $Dereference(m);
    if (!ContainsTable(t, enc_k)) {
        call $Abort($StdError(7/*INVALID_ARGUMENTS*/, 101/*ENOT_FOUND*/));
    } else {
        dst := $Mutation(l#$Mutation(m), ExtendVec(p#$Mutation(m), enc_k), GetTable(t, enc_k));
        m' := m;
    }
}
function {:inline} $1_simple_map_spec_len'address_$1_account_SignerCapability'(t: (Table int ($1_account_SignerCapability))): int {
    LenTable(t)
}
function {:inline} $1_simple_map_spec_contains_key'address_$1_account_SignerCapability'(t: (Table int ($1_account_SignerCapability)), k: int): bool {
    ContainsTable(t, $EncodeKey'address'(k))
}
function {:inline} $1_simple_map_spec_set'address_$1_account_SignerCapability'(t: Table int ($1_account_SignerCapability), k: int, v: $1_account_SignerCapability): Table int ($1_account_SignerCapability) {
    (var enc_k := $EncodeKey'address'(k);
    if (ContainsTable(t, enc_k)) then
        UpdateTable(t, enc_k, v)
    else
        AddTable(t, enc_k, v))
}
function {:inline} $1_simple_map_spec_remove'address_$1_account_SignerCapability'(t: Table int ($1_account_SignerCapability), k: int): Table int ($1_account_SignerCapability) {
    RemoveTable(t, $EncodeKey'address'(k))
}
function {:inline} $1_simple_map_spec_get'address_$1_account_SignerCapability'(t: Table int ($1_account_SignerCapability), k: int): $1_account_SignerCapability {
    GetTable(t, $EncodeKey'address'(k))
}



// ----------------------------------------------------------------------------------
// Native Table implementation for type `($1_string_String,vec'u8')`

function $IsEqual'$1_simple_map_SimpleMap'$1_string_String_vec'u8'''(t1: Table int (Vec (int)), t2: Table int (Vec (int))): bool {
    LenTable(t1) == LenTable(t2) &&
    (forall k: int :: ContainsTable(t1, k) <==> ContainsTable(t2, k)) &&
    (forall k: int :: ContainsTable(t1, k) ==> GetTable(t1, k) == GetTable(t2, k)) &&
    (forall k: int :: ContainsTable(t2, k) ==> GetTable(t1, k) == GetTable(t2, k))
}

// Not inlined.
function $IsValid'$1_simple_map_SimpleMap'$1_string_String_vec'u8'''(t: Table int (Vec (int))): bool {
    $IsValid'u64'(LenTable(t)) &&
    (forall i: int:: ContainsTable(t, i) ==> $IsValid'vec'u8''(GetTable(t, i)))
}
procedure {:inline 2} $1_simple_map_create'$1_string_String_vec'u8''() returns (v: Table int (Vec (int))) {
    v := EmptyTable();
}
procedure {:inline 2} $1_simple_map_destroy_empty'$1_string_String_vec'u8''(t: Table int (Vec (int))) {
    if (LenTable(t) != 0) {
        call $Abort($StdError(1/*INVALID_STATE*/, 102/*ENOT_EMPTY*/));
    }
}
procedure {:inline 2} $1_simple_map_length'$1_string_String_vec'u8''(t: (Table int (Vec (int)))) returns (l: int) {
    l := LenTable(t);
}
procedure {:inline 2} $1_simple_map_contains_key'$1_string_String_vec'u8''(t: (Table int (Vec (int))), k: $1_string_String) returns (r: bool) {
    r := ContainsTable(t, $EncodeKey'$1_string_String'(k));
}
procedure {:inline 2} $1_simple_map_add'$1_string_String_vec'u8''(m: $Mutation (Table int (Vec (int))), k: $1_string_String, v: Vec (int)) returns (m': $Mutation(Table int (Vec (int)))) {
    var enc_k: int;
    var t: Table int (Vec (int));
    enc_k := $EncodeKey'$1_string_String'(k);
    t := $Dereference(m);
    if (ContainsTable(t, enc_k)) {
        call $Abort($StdError(7/*INVALID_ARGUMENTS*/, 100/*EALREADY_EXISTS*/));
    } else {
        m' := $UpdateMutation(m, AddTable(t, enc_k, v));
    }
}
procedure {:inline 2} $1_simple_map_remove'$1_string_String_vec'u8''(m: $Mutation (Table int (Vec (int))), k: $1_string_String)
returns (k': $1_string_String, v: Vec (int), m': $Mutation(Table int (Vec (int)))) {
    var enc_k: int;
    var t: Table int (Vec (int));
    enc_k := $EncodeKey'$1_string_String'(k);
    t := $Dereference(m);
    if (!ContainsTable(t, enc_k)) {
        call $Abort($StdError(7/*INVALID_ARGUMENTS*/, 101/*ENOT_FOUND*/));
    } else {
        k' := k;
        v := GetTable(t, enc_k);
        m' := $UpdateMutation(m, RemoveTable(t, enc_k));
    }
}
procedure {:inline 2} $1_simple_map_borrow'$1_string_String_vec'u8''(t: Table int (Vec (int)), k: $1_string_String) returns (v: Vec (int)) {
    var enc_k: int;
    enc_k := $EncodeKey'$1_string_String'(k);
    if (!ContainsTable(t, enc_k)) {
        call $Abort($StdError(7/*INVALID_ARGUMENTS*/, 101/*ENOT_FOUND*/));
    } else {
        v := GetTable(t, $EncodeKey'$1_string_String'(k));
    }
}
procedure {:inline 2} $1_simple_map_borrow_mut'$1_string_String_vec'u8''(m: $Mutation (Table int (Vec (int))), k: $1_string_String)
returns (dst: $Mutation (Vec (int)), m': $Mutation (Table int (Vec (int)))) {
    var enc_k: int;
    var t: Table int (Vec (int));
    enc_k := $EncodeKey'$1_string_String'(k);
    t := $Dereference(m);
    if (!ContainsTable(t, enc_k)) {
        call $Abort($StdError(7/*INVALID_ARGUMENTS*/, 101/*ENOT_FOUND*/));
    } else {
        dst := $Mutation(l#$Mutation(m), ExtendVec(p#$Mutation(m), enc_k), GetTable(t, enc_k));
        m' := m;
    }
}
function {:inline} $1_simple_map_spec_len'$1_string_String_vec'u8''(t: (Table int (Vec (int)))): int {
    LenTable(t)
}
function {:inline} $1_simple_map_spec_contains_key'$1_string_String_vec'u8''(t: (Table int (Vec (int))), k: $1_string_String): bool {
    ContainsTable(t, $EncodeKey'$1_string_String'(k))
}
function {:inline} $1_simple_map_spec_set'$1_string_String_vec'u8''(t: Table int (Vec (int)), k: $1_string_String, v: Vec (int)): Table int (Vec (int)) {
    (var enc_k := $EncodeKey'$1_string_String'(k);
    if (ContainsTable(t, enc_k)) then
        UpdateTable(t, enc_k, v)
    else
        AddTable(t, enc_k, v))
}
function {:inline} $1_simple_map_spec_remove'$1_string_String_vec'u8''(t: Table int (Vec (int)), k: $1_string_String): Table int (Vec (int)) {
    RemoveTable(t, $EncodeKey'$1_string_String'(k))
}
function {:inline} $1_simple_map_spec_get'$1_string_String_vec'u8''(t: Table int (Vec (int)), k: $1_string_String): Vec (int) {
    GetTable(t, $EncodeKey'$1_string_String'(k))
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

// ----------------------------------------------------------------------------------
// Native BCS implementation for element type `bool`

// Serialize is modeled as an uninterpreted function, with an additional
// axiom to say it's an injection.

function $1_bcs_serialize'bool'(v: bool): Vec int;

axiom (forall v1, v2: bool :: {$1_bcs_serialize'bool'(v1), $1_bcs_serialize'bool'(v2)}
   $IsEqual'bool'(v1, v2) <==> $IsEqual'vec'u8''($1_bcs_serialize'bool'(v1), $1_bcs_serialize'bool'(v2)));

// This says that serialize returns a non-empty vec<u8>

axiom (forall v: bool :: {$1_bcs_serialize'bool'(v)}
     ( var r := $1_bcs_serialize'bool'(v); $IsValid'vec'u8''(r) && LenVec(r) > 0 ));


procedure $1_bcs_to_bytes'bool'(v: bool) returns (res: Vec int);
ensures res == $1_bcs_serialize'bool'(v);

function {:inline} $1_bcs_$to_bytes'bool'(v: bool): Vec int {
    $1_bcs_serialize'bool'(v)
}





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

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:14:9+116, instance <u8>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'u8'($1_from_bcs_deserialize'u8'(b1), $1_from_bcs_deserialize'u8'(b2)) ==> $IsEqual'vec'u8''(b1, b2))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:14:9+116, instance <u64>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'u64'($1_from_bcs_deserialize'u64'(b1), $1_from_bcs_deserialize'u64'(b2)) ==> $IsEqual'vec'u8''(b1, b2))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:14:9+116, instance <u128>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'u128'($1_from_bcs_deserialize'u128'(b1), $1_from_bcs_deserialize'u128'(b2)) ==> $IsEqual'vec'u8''(b1, b2))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:14:9+116, instance <u256>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'u256'($1_from_bcs_deserialize'u256'(b1), $1_from_bcs_deserialize'u256'(b2)) ==> $IsEqual'vec'u8''(b1, b2))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:14:9+116, instance <address>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'address'($1_from_bcs_deserialize'address'(b1), $1_from_bcs_deserialize'address'(b2)) ==> $IsEqual'vec'u8''(b1, b2))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:14:9+116, instance <signer>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'signer'($1_from_bcs_deserialize'signer'(b1), $1_from_bcs_deserialize'signer'(b2)) ==> $IsEqual'vec'u8''(b1, b2))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:14:9+116, instance <vector<u8>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''($1_from_bcs_deserialize'vec'u8''(b1), $1_from_bcs_deserialize'vec'u8''(b2)) ==> $IsEqual'vec'u8''(b1, b2))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:14:9+116, instance <vector<u64>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u64''($1_from_bcs_deserialize'vec'u64''(b1), $1_from_bcs_deserialize'vec'u64''(b2)) ==> $IsEqual'vec'u8''(b1, b2))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:14:9+116, instance <vector<u128>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u128''($1_from_bcs_deserialize'vec'u128''(b1), $1_from_bcs_deserialize'vec'u128''(b2)) ==> $IsEqual'vec'u8''(b1, b2))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:14:9+116, instance <vector<stake::IndividualValidatorPerformance>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'$1_stake_IndividualValidatorPerformance''($1_from_bcs_deserialize'vec'$1_stake_IndividualValidatorPerformance''(b1), $1_from_bcs_deserialize'vec'$1_stake_IndividualValidatorPerformance''(b2)) ==> $IsEqual'vec'u8''(b1, b2))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:14:9+116, instance <vector<stake::ValidatorInfo>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'$1_stake_ValidatorInfo''($1_from_bcs_deserialize'vec'$1_stake_ValidatorInfo''(b1), $1_from_bcs_deserialize'vec'$1_stake_ValidatorInfo''(b2)) ==> $IsEqual'vec'u8''(b1, b2))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:14:9+116, instance <vector<storage_gas::Point>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'$1_storage_gas_Point''($1_from_bcs_deserialize'vec'$1_storage_gas_Point''(b1), $1_from_bcs_deserialize'vec'$1_storage_gas_Point''(b2)) ==> $IsEqual'vec'u8''(b1, b2))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:14:9+116, instance <vector<governance_proposal::GovernanceProposal>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'$1_governance_proposal_GovernanceProposal''($1_from_bcs_deserialize'vec'$1_governance_proposal_GovernanceProposal''(b1), $1_from_bcs_deserialize'vec'$1_governance_proposal_GovernanceProposal''(b2)) ==> $IsEqual'vec'u8''(b1, b2))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:14:9+116, instance <vector<#0>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'#0''($1_from_bcs_deserialize'vec'#0''(b1), $1_from_bcs_deserialize'vec'#0''(b2)) ==> $IsEqual'vec'u8''(b1, b2))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:14:9+116, instance <option::Option<u128>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'$1_option_Option'u128''($1_from_bcs_deserialize'$1_option_Option'u128''(b1), $1_from_bcs_deserialize'$1_option_Option'u128''(b2)) ==> $IsEqual'vec'u8''(b1, b2))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:14:9+116, instance <option::Option<governance_proposal::GovernanceProposal>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'$1_option_Option'$1_governance_proposal_GovernanceProposal''($1_from_bcs_deserialize'$1_option_Option'$1_governance_proposal_GovernanceProposal''(b1), $1_from_bcs_deserialize'$1_option_Option'$1_governance_proposal_GovernanceProposal''(b2)) ==> $IsEqual'vec'u8''(b1, b2))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:14:9+116, instance <string::String>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'$1_string_String'($1_from_bcs_deserialize'$1_string_String'(b1), $1_from_bcs_deserialize'$1_string_String'(b2)) ==> $IsEqual'vec'u8''(b1, b2))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:14:9+116, instance <type_info::TypeInfo>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'$1_type_info_TypeInfo'($1_from_bcs_deserialize'$1_type_info_TypeInfo'(b1), $1_from_bcs_deserialize'$1_type_info_TypeInfo'(b2)) ==> $IsEqual'vec'u8''(b1, b2))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:14:9+116, instance <table::Table<u64, voting::Proposal<governance_proposal::GovernanceProposal>>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'$1_table_Table'u64_$1_voting_Proposal'$1_governance_proposal_GovernanceProposal'''($1_from_bcs_deserialize'$1_table_Table'u64_$1_voting_Proposal'$1_governance_proposal_GovernanceProposal'''(b1), $1_from_bcs_deserialize'$1_table_Table'u64_$1_voting_Proposal'$1_governance_proposal_GovernanceProposal'''(b2)) ==> $IsEqual'vec'u8''(b1, b2))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:14:9+116, instance <guid::GUID>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'$1_guid_GUID'($1_from_bcs_deserialize'$1_guid_GUID'(b1), $1_from_bcs_deserialize'$1_guid_GUID'(b2)) ==> $IsEqual'vec'u8''(b1, b2))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:14:9+116, instance <guid::ID>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'$1_guid_ID'($1_from_bcs_deserialize'$1_guid_ID'(b1), $1_from_bcs_deserialize'$1_guid_ID'(b2)) ==> $IsEqual'vec'u8''(b1, b2))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:14:9+116, instance <event::EventHandle<voting::CreateProposalEvent>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'$1_event_EventHandle'$1_voting_CreateProposalEvent''($1_from_bcs_deserialize'$1_event_EventHandle'$1_voting_CreateProposalEvent''(b1), $1_from_bcs_deserialize'$1_event_EventHandle'$1_voting_CreateProposalEvent''(b2)) ==> $IsEqual'vec'u8''(b1, b2))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:14:9+116, instance <event::EventHandle<voting::RegisterForumEvent>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'$1_event_EventHandle'$1_voting_RegisterForumEvent''($1_from_bcs_deserialize'$1_event_EventHandle'$1_voting_RegisterForumEvent''(b1), $1_from_bcs_deserialize'$1_event_EventHandle'$1_voting_RegisterForumEvent''(b2)) ==> $IsEqual'vec'u8''(b1, b2))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:14:9+116, instance <event::EventHandle<voting::ResolveProposal>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'$1_event_EventHandle'$1_voting_ResolveProposal''($1_from_bcs_deserialize'$1_event_EventHandle'$1_voting_ResolveProposal''(b1), $1_from_bcs_deserialize'$1_event_EventHandle'$1_voting_ResolveProposal''(b2)) ==> $IsEqual'vec'u8''(b1, b2))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:14:9+116, instance <event::EventHandle<voting::VoteEvent>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'$1_event_EventHandle'$1_voting_VoteEvent''($1_from_bcs_deserialize'$1_event_EventHandle'$1_voting_VoteEvent''(b1), $1_from_bcs_deserialize'$1_event_EventHandle'$1_voting_VoteEvent''(b2)) ==> $IsEqual'vec'u8''(b1, b2))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:14:9+116, instance <event::EventHandle<reconfiguration::NewEpochEvent>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'$1_event_EventHandle'$1_reconfiguration_NewEpochEvent''($1_from_bcs_deserialize'$1_event_EventHandle'$1_reconfiguration_NewEpochEvent''(b1), $1_from_bcs_deserialize'$1_event_EventHandle'$1_reconfiguration_NewEpochEvent''(b2)) ==> $IsEqual'vec'u8''(b1, b2))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:14:9+116, instance <event::EventHandle<block::NewBlockEvent>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'$1_event_EventHandle'$1_block_NewBlockEvent''($1_from_bcs_deserialize'$1_event_EventHandle'$1_block_NewBlockEvent''(b1), $1_from_bcs_deserialize'$1_event_EventHandle'$1_block_NewBlockEvent''(b2)) ==> $IsEqual'vec'u8''(b1, b2))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:14:9+116, instance <event::EventHandle<block::UpdateEpochIntervalEvent>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'$1_event_EventHandle'$1_block_UpdateEpochIntervalEvent''($1_from_bcs_deserialize'$1_event_EventHandle'$1_block_UpdateEpochIntervalEvent''(b1), $1_from_bcs_deserialize'$1_event_EventHandle'$1_block_UpdateEpochIntervalEvent''(b2)) ==> $IsEqual'vec'u8''(b1, b2))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:14:9+116, instance <account::SignerCapability>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'$1_account_SignerCapability'($1_from_bcs_deserialize'$1_account_SignerCapability'(b1), $1_from_bcs_deserialize'$1_account_SignerCapability'(b2)) ==> $IsEqual'vec'u8''(b1, b2))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:14:9+116, instance <coin::BurnCapability<aptos_coin::AptosCoin>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'$1_coin_BurnCapability'$1_aptos_coin_AptosCoin''($1_from_bcs_deserialize'$1_coin_BurnCapability'$1_aptos_coin_AptosCoin''(b1), $1_from_bcs_deserialize'$1_coin_BurnCapability'$1_aptos_coin_AptosCoin''(b2)) ==> $IsEqual'vec'u8''(b1, b2))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:14:9+116, instance <coin::MintCapability<aptos_coin::AptosCoin>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'$1_coin_MintCapability'$1_aptos_coin_AptosCoin''($1_from_bcs_deserialize'$1_coin_MintCapability'$1_aptos_coin_AptosCoin''(b1), $1_from_bcs_deserialize'$1_coin_MintCapability'$1_aptos_coin_AptosCoin''(b2)) ==> $IsEqual'vec'u8''(b1, b2))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:14:9+116, instance <chain_status::GenesisEndMarker>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'$1_chain_status_GenesisEndMarker'($1_from_bcs_deserialize'$1_chain_status_GenesisEndMarker'(b1), $1_from_bcs_deserialize'$1_chain_status_GenesisEndMarker'(b2)) ==> $IsEqual'vec'u8''(b1, b2))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:14:9+116, instance <timestamp::CurrentTimeMicroseconds>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'$1_timestamp_CurrentTimeMicroseconds'($1_from_bcs_deserialize'$1_timestamp_CurrentTimeMicroseconds'(b1), $1_from_bcs_deserialize'$1_timestamp_CurrentTimeMicroseconds'(b2)) ==> $IsEqual'vec'u8''(b1, b2))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:14:9+116, instance <simple_map::SimpleMap<u64, vector<u8>>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'$1_simple_map_SimpleMap'u64_vec'u8'''($1_from_bcs_deserialize'$1_simple_map_SimpleMap'u64_vec'u8'''(b1), $1_from_bcs_deserialize'$1_simple_map_SimpleMap'u64_vec'u8'''(b2)) ==> $IsEqual'vec'u8''(b1, b2))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:14:9+116, instance <simple_map::SimpleMap<address, account::SignerCapability>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'$1_simple_map_SimpleMap'address_$1_account_SignerCapability''($1_from_bcs_deserialize'$1_simple_map_SimpleMap'address_$1_account_SignerCapability''(b1), $1_from_bcs_deserialize'$1_simple_map_SimpleMap'address_$1_account_SignerCapability''(b2)) ==> $IsEqual'vec'u8''(b1, b2))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:14:9+116, instance <simple_map::SimpleMap<string::String, vector<u8>>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'$1_simple_map_SimpleMap'$1_string_String_vec'u8'''($1_from_bcs_deserialize'$1_simple_map_SimpleMap'$1_string_String_vec'u8'''(b1), $1_from_bcs_deserialize'$1_simple_map_SimpleMap'$1_string_String_vec'u8'''(b2)) ==> $IsEqual'vec'u8''(b1, b2))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:14:9+116, instance <voting::Proposal<governance_proposal::GovernanceProposal>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'$1_voting_Proposal'$1_governance_proposal_GovernanceProposal''($1_from_bcs_deserialize'$1_voting_Proposal'$1_governance_proposal_GovernanceProposal''(b1), $1_from_bcs_deserialize'$1_voting_Proposal'$1_governance_proposal_GovernanceProposal''(b2)) ==> $IsEqual'vec'u8''(b1, b2))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:14:9+116, instance <voting::ResolveProposal>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'$1_voting_ResolveProposal'($1_from_bcs_deserialize'$1_voting_ResolveProposal'(b1), $1_from_bcs_deserialize'$1_voting_ResolveProposal'(b2)) ==> $IsEqual'vec'u8''(b1, b2))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:14:9+116, instance <voting::VotingEvents>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'$1_voting_VotingEvents'($1_from_bcs_deserialize'$1_voting_VotingEvents'(b1), $1_from_bcs_deserialize'$1_voting_VotingEvents'(b2)) ==> $IsEqual'vec'u8''(b1, b2))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:14:9+116, instance <voting::VotingForum<governance_proposal::GovernanceProposal>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'$1_voting_VotingForum'$1_governance_proposal_GovernanceProposal''($1_from_bcs_deserialize'$1_voting_VotingForum'$1_governance_proposal_GovernanceProposal''(b1), $1_from_bcs_deserialize'$1_voting_VotingForum'$1_governance_proposal_GovernanceProposal''(b2)) ==> $IsEqual'vec'u8''(b1, b2))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:14:9+116, instance <staking_config::StakingConfig>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'$1_staking_config_StakingConfig'($1_from_bcs_deserialize'$1_staking_config_StakingConfig'(b1), $1_from_bcs_deserialize'$1_staking_config_StakingConfig'(b2)) ==> $IsEqual'vec'u8''(b1, b2))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:14:9+116, instance <stake::AptosCoinCapabilities>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'$1_stake_AptosCoinCapabilities'($1_from_bcs_deserialize'$1_stake_AptosCoinCapabilities'(b1), $1_from_bcs_deserialize'$1_stake_AptosCoinCapabilities'(b2)) ==> $IsEqual'vec'u8''(b1, b2))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:14:9+116, instance <stake::ValidatorConfig>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'$1_stake_ValidatorConfig'($1_from_bcs_deserialize'$1_stake_ValidatorConfig'(b1), $1_from_bcs_deserialize'$1_stake_ValidatorConfig'(b2)) ==> $IsEqual'vec'u8''(b1, b2))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:14:9+116, instance <stake::ValidatorPerformance>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'$1_stake_ValidatorPerformance'($1_from_bcs_deserialize'$1_stake_ValidatorPerformance'(b1), $1_from_bcs_deserialize'$1_stake_ValidatorPerformance'(b2)) ==> $IsEqual'vec'u8''(b1, b2))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:14:9+116, instance <stake::ValidatorSet>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'$1_stake_ValidatorSet'($1_from_bcs_deserialize'$1_stake_ValidatorSet'(b1), $1_from_bcs_deserialize'$1_stake_ValidatorSet'(b2)) ==> $IsEqual'vec'u8''(b1, b2))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:14:9+116, instance <transaction_fee::AptosCoinCapabilities>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'$1_transaction_fee_AptosCoinCapabilities'($1_from_bcs_deserialize'$1_transaction_fee_AptosCoinCapabilities'(b1), $1_from_bcs_deserialize'$1_transaction_fee_AptosCoinCapabilities'(b2)) ==> $IsEqual'vec'u8''(b1, b2))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:14:9+116, instance <state_storage::GasParameter>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'$1_state_storage_GasParameter'($1_from_bcs_deserialize'$1_state_storage_GasParameter'(b1), $1_from_bcs_deserialize'$1_state_storage_GasParameter'(b2)) ==> $IsEqual'vec'u8''(b1, b2))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:14:9+116, instance <state_storage::StateStorageUsage>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'$1_state_storage_StateStorageUsage'($1_from_bcs_deserialize'$1_state_storage_StateStorageUsage'(b1), $1_from_bcs_deserialize'$1_state_storage_StateStorageUsage'(b2)) ==> $IsEqual'vec'u8''(b1, b2))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:14:9+116, instance <state_storage::Usage>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'$1_state_storage_Usage'($1_from_bcs_deserialize'$1_state_storage_Usage'(b1), $1_from_bcs_deserialize'$1_state_storage_Usage'(b2)) ==> $IsEqual'vec'u8''(b1, b2))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:14:9+116, instance <storage_gas::GasCurve>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'$1_storage_gas_GasCurve'($1_from_bcs_deserialize'$1_storage_gas_GasCurve'(b1), $1_from_bcs_deserialize'$1_storage_gas_GasCurve'(b2)) ==> $IsEqual'vec'u8''(b1, b2))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:14:9+116, instance <storage_gas::Point>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'$1_storage_gas_Point'($1_from_bcs_deserialize'$1_storage_gas_Point'(b1), $1_from_bcs_deserialize'$1_storage_gas_Point'(b2)) ==> $IsEqual'vec'u8''(b1, b2))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:14:9+116, instance <storage_gas::StorageGas>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'$1_storage_gas_StorageGas'($1_from_bcs_deserialize'$1_storage_gas_StorageGas'(b1), $1_from_bcs_deserialize'$1_storage_gas_StorageGas'(b2)) ==> $IsEqual'vec'u8''(b1, b2))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:14:9+116, instance <storage_gas::StorageGasConfig>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'$1_storage_gas_StorageGasConfig'($1_from_bcs_deserialize'$1_storage_gas_StorageGasConfig'(b1), $1_from_bcs_deserialize'$1_storage_gas_StorageGasConfig'(b2)) ==> $IsEqual'vec'u8''(b1, b2))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:14:9+116, instance <storage_gas::UsageGasConfig>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'$1_storage_gas_UsageGasConfig'($1_from_bcs_deserialize'$1_storage_gas_UsageGasConfig'(b1), $1_from_bcs_deserialize'$1_storage_gas_UsageGasConfig'(b2)) ==> $IsEqual'vec'u8''(b1, b2))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:14:9+116, instance <reconfiguration::Configuration>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'$1_reconfiguration_Configuration'($1_from_bcs_deserialize'$1_reconfiguration_Configuration'(b1), $1_from_bcs_deserialize'$1_reconfiguration_Configuration'(b2)) ==> $IsEqual'vec'u8''(b1, b2))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:14:9+116, instance <governance_proposal::GovernanceProposal>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'$1_governance_proposal_GovernanceProposal'($1_from_bcs_deserialize'$1_governance_proposal_GovernanceProposal'(b1), $1_from_bcs_deserialize'$1_governance_proposal_GovernanceProposal'(b2)) ==> $IsEqual'vec'u8''(b1, b2))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:14:9+116, instance <aptos_governance::ApprovedExecutionHashes>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'$1_aptos_governance_ApprovedExecutionHashes'($1_from_bcs_deserialize'$1_aptos_governance_ApprovedExecutionHashes'(b1), $1_from_bcs_deserialize'$1_aptos_governance_ApprovedExecutionHashes'(b2)) ==> $IsEqual'vec'u8''(b1, b2))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:14:9+116, instance <aptos_governance::GovernanceResponsbility>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'$1_aptos_governance_GovernanceResponsbility'($1_from_bcs_deserialize'$1_aptos_governance_GovernanceResponsbility'(b1), $1_from_bcs_deserialize'$1_aptos_governance_GovernanceResponsbility'(b2)) ==> $IsEqual'vec'u8''(b1, b2))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:14:9+116, instance <block::BlockResource>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'$1_block_BlockResource'($1_from_bcs_deserialize'$1_block_BlockResource'(b1), $1_from_bcs_deserialize'$1_block_BlockResource'(b2)) ==> $IsEqual'vec'u8''(b1, b2))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:14:9+116, instance <#0>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'#0'($1_from_bcs_deserialize'#0'(b1), $1_from_bcs_deserialize'#0'(b2)) ==> $IsEqual'vec'u8''(b1, b2))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:18:9+124, instance <bool>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'bool'($1_from_bcs_deserializable'bool'(b1), $1_from_bcs_deserializable'bool'(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:18:9+124, instance <u8>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'bool'($1_from_bcs_deserializable'u8'(b1), $1_from_bcs_deserializable'u8'(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:18:9+124, instance <u64>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'bool'($1_from_bcs_deserializable'u64'(b1), $1_from_bcs_deserializable'u64'(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:18:9+124, instance <u128>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'bool'($1_from_bcs_deserializable'u128'(b1), $1_from_bcs_deserializable'u128'(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:18:9+124, instance <u256>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'bool'($1_from_bcs_deserializable'u256'(b1), $1_from_bcs_deserializable'u256'(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:18:9+124, instance <address>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'bool'($1_from_bcs_deserializable'address'(b1), $1_from_bcs_deserializable'address'(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:18:9+124, instance <signer>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'bool'($1_from_bcs_deserializable'signer'(b1), $1_from_bcs_deserializable'signer'(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:18:9+124, instance <vector<u8>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'bool'($1_from_bcs_deserializable'vec'u8''(b1), $1_from_bcs_deserializable'vec'u8''(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:18:9+124, instance <vector<u64>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'bool'($1_from_bcs_deserializable'vec'u64''(b1), $1_from_bcs_deserializable'vec'u64''(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:18:9+124, instance <vector<u128>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'bool'($1_from_bcs_deserializable'vec'u128''(b1), $1_from_bcs_deserializable'vec'u128''(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:18:9+124, instance <vector<stake::IndividualValidatorPerformance>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'bool'($1_from_bcs_deserializable'vec'$1_stake_IndividualValidatorPerformance''(b1), $1_from_bcs_deserializable'vec'$1_stake_IndividualValidatorPerformance''(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:18:9+124, instance <vector<stake::ValidatorInfo>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'bool'($1_from_bcs_deserializable'vec'$1_stake_ValidatorInfo''(b1), $1_from_bcs_deserializable'vec'$1_stake_ValidatorInfo''(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:18:9+124, instance <vector<storage_gas::Point>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'bool'($1_from_bcs_deserializable'vec'$1_storage_gas_Point''(b1), $1_from_bcs_deserializable'vec'$1_storage_gas_Point''(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:18:9+124, instance <vector<governance_proposal::GovernanceProposal>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'bool'($1_from_bcs_deserializable'vec'$1_governance_proposal_GovernanceProposal''(b1), $1_from_bcs_deserializable'vec'$1_governance_proposal_GovernanceProposal''(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:18:9+124, instance <vector<#0>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'bool'($1_from_bcs_deserializable'vec'#0''(b1), $1_from_bcs_deserializable'vec'#0''(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:18:9+124, instance <option::Option<u128>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'bool'($1_from_bcs_deserializable'$1_option_Option'u128''(b1), $1_from_bcs_deserializable'$1_option_Option'u128''(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:18:9+124, instance <option::Option<governance_proposal::GovernanceProposal>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'bool'($1_from_bcs_deserializable'$1_option_Option'$1_governance_proposal_GovernanceProposal''(b1), $1_from_bcs_deserializable'$1_option_Option'$1_governance_proposal_GovernanceProposal''(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:18:9+124, instance <string::String>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'bool'($1_from_bcs_deserializable'$1_string_String'(b1), $1_from_bcs_deserializable'$1_string_String'(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:18:9+124, instance <type_info::TypeInfo>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'bool'($1_from_bcs_deserializable'$1_type_info_TypeInfo'(b1), $1_from_bcs_deserializable'$1_type_info_TypeInfo'(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:18:9+124, instance <table::Table<u64, voting::Proposal<governance_proposal::GovernanceProposal>>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'bool'($1_from_bcs_deserializable'$1_table_Table'u64_$1_voting_Proposal'$1_governance_proposal_GovernanceProposal'''(b1), $1_from_bcs_deserializable'$1_table_Table'u64_$1_voting_Proposal'$1_governance_proposal_GovernanceProposal'''(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:18:9+124, instance <guid::GUID>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'bool'($1_from_bcs_deserializable'$1_guid_GUID'(b1), $1_from_bcs_deserializable'$1_guid_GUID'(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:18:9+124, instance <guid::ID>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'bool'($1_from_bcs_deserializable'$1_guid_ID'(b1), $1_from_bcs_deserializable'$1_guid_ID'(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:18:9+124, instance <event::EventHandle<voting::CreateProposalEvent>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'bool'($1_from_bcs_deserializable'$1_event_EventHandle'$1_voting_CreateProposalEvent''(b1), $1_from_bcs_deserializable'$1_event_EventHandle'$1_voting_CreateProposalEvent''(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:18:9+124, instance <event::EventHandle<voting::RegisterForumEvent>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'bool'($1_from_bcs_deserializable'$1_event_EventHandle'$1_voting_RegisterForumEvent''(b1), $1_from_bcs_deserializable'$1_event_EventHandle'$1_voting_RegisterForumEvent''(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:18:9+124, instance <event::EventHandle<voting::ResolveProposal>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'bool'($1_from_bcs_deserializable'$1_event_EventHandle'$1_voting_ResolveProposal''(b1), $1_from_bcs_deserializable'$1_event_EventHandle'$1_voting_ResolveProposal''(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:18:9+124, instance <event::EventHandle<voting::VoteEvent>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'bool'($1_from_bcs_deserializable'$1_event_EventHandle'$1_voting_VoteEvent''(b1), $1_from_bcs_deserializable'$1_event_EventHandle'$1_voting_VoteEvent''(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:18:9+124, instance <event::EventHandle<reconfiguration::NewEpochEvent>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'bool'($1_from_bcs_deserializable'$1_event_EventHandle'$1_reconfiguration_NewEpochEvent''(b1), $1_from_bcs_deserializable'$1_event_EventHandle'$1_reconfiguration_NewEpochEvent''(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:18:9+124, instance <event::EventHandle<block::NewBlockEvent>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'bool'($1_from_bcs_deserializable'$1_event_EventHandle'$1_block_NewBlockEvent''(b1), $1_from_bcs_deserializable'$1_event_EventHandle'$1_block_NewBlockEvent''(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:18:9+124, instance <event::EventHandle<block::UpdateEpochIntervalEvent>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'bool'($1_from_bcs_deserializable'$1_event_EventHandle'$1_block_UpdateEpochIntervalEvent''(b1), $1_from_bcs_deserializable'$1_event_EventHandle'$1_block_UpdateEpochIntervalEvent''(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:18:9+124, instance <account::SignerCapability>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'bool'($1_from_bcs_deserializable'$1_account_SignerCapability'(b1), $1_from_bcs_deserializable'$1_account_SignerCapability'(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:18:9+124, instance <coin::BurnCapability<aptos_coin::AptosCoin>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'bool'($1_from_bcs_deserializable'$1_coin_BurnCapability'$1_aptos_coin_AptosCoin''(b1), $1_from_bcs_deserializable'$1_coin_BurnCapability'$1_aptos_coin_AptosCoin''(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:18:9+124, instance <coin::MintCapability<aptos_coin::AptosCoin>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'bool'($1_from_bcs_deserializable'$1_coin_MintCapability'$1_aptos_coin_AptosCoin''(b1), $1_from_bcs_deserializable'$1_coin_MintCapability'$1_aptos_coin_AptosCoin''(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:18:9+124, instance <chain_status::GenesisEndMarker>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'bool'($1_from_bcs_deserializable'$1_chain_status_GenesisEndMarker'(b1), $1_from_bcs_deserializable'$1_chain_status_GenesisEndMarker'(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:18:9+124, instance <timestamp::CurrentTimeMicroseconds>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'bool'($1_from_bcs_deserializable'$1_timestamp_CurrentTimeMicroseconds'(b1), $1_from_bcs_deserializable'$1_timestamp_CurrentTimeMicroseconds'(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:18:9+124, instance <simple_map::SimpleMap<u64, vector<u8>>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'bool'($1_from_bcs_deserializable'$1_simple_map_SimpleMap'u64_vec'u8'''(b1), $1_from_bcs_deserializable'$1_simple_map_SimpleMap'u64_vec'u8'''(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:18:9+124, instance <simple_map::SimpleMap<address, account::SignerCapability>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'bool'($1_from_bcs_deserializable'$1_simple_map_SimpleMap'address_$1_account_SignerCapability''(b1), $1_from_bcs_deserializable'$1_simple_map_SimpleMap'address_$1_account_SignerCapability''(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:18:9+124, instance <simple_map::SimpleMap<string::String, vector<u8>>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'bool'($1_from_bcs_deserializable'$1_simple_map_SimpleMap'$1_string_String_vec'u8'''(b1), $1_from_bcs_deserializable'$1_simple_map_SimpleMap'$1_string_String_vec'u8'''(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:18:9+124, instance <voting::Proposal<governance_proposal::GovernanceProposal>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'bool'($1_from_bcs_deserializable'$1_voting_Proposal'$1_governance_proposal_GovernanceProposal''(b1), $1_from_bcs_deserializable'$1_voting_Proposal'$1_governance_proposal_GovernanceProposal''(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:18:9+124, instance <voting::ResolveProposal>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'bool'($1_from_bcs_deserializable'$1_voting_ResolveProposal'(b1), $1_from_bcs_deserializable'$1_voting_ResolveProposal'(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:18:9+124, instance <voting::VotingEvents>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'bool'($1_from_bcs_deserializable'$1_voting_VotingEvents'(b1), $1_from_bcs_deserializable'$1_voting_VotingEvents'(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:18:9+124, instance <voting::VotingForum<governance_proposal::GovernanceProposal>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'bool'($1_from_bcs_deserializable'$1_voting_VotingForum'$1_governance_proposal_GovernanceProposal''(b1), $1_from_bcs_deserializable'$1_voting_VotingForum'$1_governance_proposal_GovernanceProposal''(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:18:9+124, instance <staking_config::StakingConfig>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'bool'($1_from_bcs_deserializable'$1_staking_config_StakingConfig'(b1), $1_from_bcs_deserializable'$1_staking_config_StakingConfig'(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:18:9+124, instance <stake::AptosCoinCapabilities>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'bool'($1_from_bcs_deserializable'$1_stake_AptosCoinCapabilities'(b1), $1_from_bcs_deserializable'$1_stake_AptosCoinCapabilities'(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:18:9+124, instance <stake::ValidatorConfig>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'bool'($1_from_bcs_deserializable'$1_stake_ValidatorConfig'(b1), $1_from_bcs_deserializable'$1_stake_ValidatorConfig'(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:18:9+124, instance <stake::ValidatorPerformance>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'bool'($1_from_bcs_deserializable'$1_stake_ValidatorPerformance'(b1), $1_from_bcs_deserializable'$1_stake_ValidatorPerformance'(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:18:9+124, instance <stake::ValidatorSet>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'bool'($1_from_bcs_deserializable'$1_stake_ValidatorSet'(b1), $1_from_bcs_deserializable'$1_stake_ValidatorSet'(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:18:9+124, instance <transaction_fee::AptosCoinCapabilities>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'bool'($1_from_bcs_deserializable'$1_transaction_fee_AptosCoinCapabilities'(b1), $1_from_bcs_deserializable'$1_transaction_fee_AptosCoinCapabilities'(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:18:9+124, instance <state_storage::GasParameter>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'bool'($1_from_bcs_deserializable'$1_state_storage_GasParameter'(b1), $1_from_bcs_deserializable'$1_state_storage_GasParameter'(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:18:9+124, instance <state_storage::StateStorageUsage>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'bool'($1_from_bcs_deserializable'$1_state_storage_StateStorageUsage'(b1), $1_from_bcs_deserializable'$1_state_storage_StateStorageUsage'(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:18:9+124, instance <state_storage::Usage>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'bool'($1_from_bcs_deserializable'$1_state_storage_Usage'(b1), $1_from_bcs_deserializable'$1_state_storage_Usage'(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:18:9+124, instance <storage_gas::GasCurve>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'bool'($1_from_bcs_deserializable'$1_storage_gas_GasCurve'(b1), $1_from_bcs_deserializable'$1_storage_gas_GasCurve'(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:18:9+124, instance <storage_gas::Point>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'bool'($1_from_bcs_deserializable'$1_storage_gas_Point'(b1), $1_from_bcs_deserializable'$1_storage_gas_Point'(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:18:9+124, instance <storage_gas::StorageGas>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'bool'($1_from_bcs_deserializable'$1_storage_gas_StorageGas'(b1), $1_from_bcs_deserializable'$1_storage_gas_StorageGas'(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:18:9+124, instance <storage_gas::StorageGasConfig>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'bool'($1_from_bcs_deserializable'$1_storage_gas_StorageGasConfig'(b1), $1_from_bcs_deserializable'$1_storage_gas_StorageGasConfig'(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:18:9+124, instance <storage_gas::UsageGasConfig>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'bool'($1_from_bcs_deserializable'$1_storage_gas_UsageGasConfig'(b1), $1_from_bcs_deserializable'$1_storage_gas_UsageGasConfig'(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:18:9+124, instance <reconfiguration::Configuration>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'bool'($1_from_bcs_deserializable'$1_reconfiguration_Configuration'(b1), $1_from_bcs_deserializable'$1_reconfiguration_Configuration'(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:18:9+124, instance <governance_proposal::GovernanceProposal>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'bool'($1_from_bcs_deserializable'$1_governance_proposal_GovernanceProposal'(b1), $1_from_bcs_deserializable'$1_governance_proposal_GovernanceProposal'(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:18:9+124, instance <aptos_governance::ApprovedExecutionHashes>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'bool'($1_from_bcs_deserializable'$1_aptos_governance_ApprovedExecutionHashes'(b1), $1_from_bcs_deserializable'$1_aptos_governance_ApprovedExecutionHashes'(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:18:9+124, instance <aptos_governance::GovernanceResponsbility>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'bool'($1_from_bcs_deserializable'$1_aptos_governance_GovernanceResponsbility'(b1), $1_from_bcs_deserializable'$1_aptos_governance_GovernanceResponsbility'(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:18:9+124, instance <block::BlockResource>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'bool'($1_from_bcs_deserializable'$1_block_BlockResource'(b1), $1_from_bcs_deserializable'$1_block_BlockResource'(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:18:9+124, instance <#0>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'bool'($1_from_bcs_deserializable'#0'(b1), $1_from_bcs_deserializable'#0'(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:21:9+118, instance <bool>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'bool'($1_from_bcs_deserialize'bool'(b1), $1_from_bcs_deserialize'bool'(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:21:9+118, instance <u8>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'u8'($1_from_bcs_deserialize'u8'(b1), $1_from_bcs_deserialize'u8'(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:21:9+118, instance <u64>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'u64'($1_from_bcs_deserialize'u64'(b1), $1_from_bcs_deserialize'u64'(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:21:9+118, instance <u128>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'u128'($1_from_bcs_deserialize'u128'(b1), $1_from_bcs_deserialize'u128'(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:21:9+118, instance <u256>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'u256'($1_from_bcs_deserialize'u256'(b1), $1_from_bcs_deserialize'u256'(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:21:9+118, instance <address>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'address'($1_from_bcs_deserialize'address'(b1), $1_from_bcs_deserialize'address'(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:21:9+118, instance <signer>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'signer'($1_from_bcs_deserialize'signer'(b1), $1_from_bcs_deserialize'signer'(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:21:9+118, instance <vector<u8>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'vec'u8''($1_from_bcs_deserialize'vec'u8''(b1), $1_from_bcs_deserialize'vec'u8''(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:21:9+118, instance <vector<u64>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'vec'u64''($1_from_bcs_deserialize'vec'u64''(b1), $1_from_bcs_deserialize'vec'u64''(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:21:9+118, instance <vector<u128>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'vec'u128''($1_from_bcs_deserialize'vec'u128''(b1), $1_from_bcs_deserialize'vec'u128''(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:21:9+118, instance <vector<stake::IndividualValidatorPerformance>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'vec'$1_stake_IndividualValidatorPerformance''($1_from_bcs_deserialize'vec'$1_stake_IndividualValidatorPerformance''(b1), $1_from_bcs_deserialize'vec'$1_stake_IndividualValidatorPerformance''(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:21:9+118, instance <vector<stake::ValidatorInfo>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'vec'$1_stake_ValidatorInfo''($1_from_bcs_deserialize'vec'$1_stake_ValidatorInfo''(b1), $1_from_bcs_deserialize'vec'$1_stake_ValidatorInfo''(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:21:9+118, instance <vector<storage_gas::Point>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'vec'$1_storage_gas_Point''($1_from_bcs_deserialize'vec'$1_storage_gas_Point''(b1), $1_from_bcs_deserialize'vec'$1_storage_gas_Point''(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:21:9+118, instance <vector<governance_proposal::GovernanceProposal>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'vec'$1_governance_proposal_GovernanceProposal''($1_from_bcs_deserialize'vec'$1_governance_proposal_GovernanceProposal''(b1), $1_from_bcs_deserialize'vec'$1_governance_proposal_GovernanceProposal''(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:21:9+118, instance <vector<#0>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'vec'#0''($1_from_bcs_deserialize'vec'#0''(b1), $1_from_bcs_deserialize'vec'#0''(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:21:9+118, instance <option::Option<u128>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'$1_option_Option'u128''($1_from_bcs_deserialize'$1_option_Option'u128''(b1), $1_from_bcs_deserialize'$1_option_Option'u128''(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:21:9+118, instance <option::Option<governance_proposal::GovernanceProposal>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'$1_option_Option'$1_governance_proposal_GovernanceProposal''($1_from_bcs_deserialize'$1_option_Option'$1_governance_proposal_GovernanceProposal''(b1), $1_from_bcs_deserialize'$1_option_Option'$1_governance_proposal_GovernanceProposal''(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:21:9+118, instance <string::String>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'$1_string_String'($1_from_bcs_deserialize'$1_string_String'(b1), $1_from_bcs_deserialize'$1_string_String'(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:21:9+118, instance <type_info::TypeInfo>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'$1_type_info_TypeInfo'($1_from_bcs_deserialize'$1_type_info_TypeInfo'(b1), $1_from_bcs_deserialize'$1_type_info_TypeInfo'(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:21:9+118, instance <table::Table<u64, voting::Proposal<governance_proposal::GovernanceProposal>>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'$1_table_Table'u64_$1_voting_Proposal'$1_governance_proposal_GovernanceProposal'''($1_from_bcs_deserialize'$1_table_Table'u64_$1_voting_Proposal'$1_governance_proposal_GovernanceProposal'''(b1), $1_from_bcs_deserialize'$1_table_Table'u64_$1_voting_Proposal'$1_governance_proposal_GovernanceProposal'''(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:21:9+118, instance <guid::GUID>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'$1_guid_GUID'($1_from_bcs_deserialize'$1_guid_GUID'(b1), $1_from_bcs_deserialize'$1_guid_GUID'(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:21:9+118, instance <guid::ID>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'$1_guid_ID'($1_from_bcs_deserialize'$1_guid_ID'(b1), $1_from_bcs_deserialize'$1_guid_ID'(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:21:9+118, instance <event::EventHandle<voting::CreateProposalEvent>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'$1_event_EventHandle'$1_voting_CreateProposalEvent''($1_from_bcs_deserialize'$1_event_EventHandle'$1_voting_CreateProposalEvent''(b1), $1_from_bcs_deserialize'$1_event_EventHandle'$1_voting_CreateProposalEvent''(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:21:9+118, instance <event::EventHandle<voting::RegisterForumEvent>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'$1_event_EventHandle'$1_voting_RegisterForumEvent''($1_from_bcs_deserialize'$1_event_EventHandle'$1_voting_RegisterForumEvent''(b1), $1_from_bcs_deserialize'$1_event_EventHandle'$1_voting_RegisterForumEvent''(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:21:9+118, instance <event::EventHandle<voting::ResolveProposal>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'$1_event_EventHandle'$1_voting_ResolveProposal''($1_from_bcs_deserialize'$1_event_EventHandle'$1_voting_ResolveProposal''(b1), $1_from_bcs_deserialize'$1_event_EventHandle'$1_voting_ResolveProposal''(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:21:9+118, instance <event::EventHandle<voting::VoteEvent>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'$1_event_EventHandle'$1_voting_VoteEvent''($1_from_bcs_deserialize'$1_event_EventHandle'$1_voting_VoteEvent''(b1), $1_from_bcs_deserialize'$1_event_EventHandle'$1_voting_VoteEvent''(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:21:9+118, instance <event::EventHandle<reconfiguration::NewEpochEvent>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'$1_event_EventHandle'$1_reconfiguration_NewEpochEvent''($1_from_bcs_deserialize'$1_event_EventHandle'$1_reconfiguration_NewEpochEvent''(b1), $1_from_bcs_deserialize'$1_event_EventHandle'$1_reconfiguration_NewEpochEvent''(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:21:9+118, instance <event::EventHandle<block::NewBlockEvent>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'$1_event_EventHandle'$1_block_NewBlockEvent''($1_from_bcs_deserialize'$1_event_EventHandle'$1_block_NewBlockEvent''(b1), $1_from_bcs_deserialize'$1_event_EventHandle'$1_block_NewBlockEvent''(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:21:9+118, instance <event::EventHandle<block::UpdateEpochIntervalEvent>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'$1_event_EventHandle'$1_block_UpdateEpochIntervalEvent''($1_from_bcs_deserialize'$1_event_EventHandle'$1_block_UpdateEpochIntervalEvent''(b1), $1_from_bcs_deserialize'$1_event_EventHandle'$1_block_UpdateEpochIntervalEvent''(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:21:9+118, instance <account::SignerCapability>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'$1_account_SignerCapability'($1_from_bcs_deserialize'$1_account_SignerCapability'(b1), $1_from_bcs_deserialize'$1_account_SignerCapability'(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:21:9+118, instance <coin::BurnCapability<aptos_coin::AptosCoin>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'$1_coin_BurnCapability'$1_aptos_coin_AptosCoin''($1_from_bcs_deserialize'$1_coin_BurnCapability'$1_aptos_coin_AptosCoin''(b1), $1_from_bcs_deserialize'$1_coin_BurnCapability'$1_aptos_coin_AptosCoin''(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:21:9+118, instance <coin::MintCapability<aptos_coin::AptosCoin>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'$1_coin_MintCapability'$1_aptos_coin_AptosCoin''($1_from_bcs_deserialize'$1_coin_MintCapability'$1_aptos_coin_AptosCoin''(b1), $1_from_bcs_deserialize'$1_coin_MintCapability'$1_aptos_coin_AptosCoin''(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:21:9+118, instance <chain_status::GenesisEndMarker>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'$1_chain_status_GenesisEndMarker'($1_from_bcs_deserialize'$1_chain_status_GenesisEndMarker'(b1), $1_from_bcs_deserialize'$1_chain_status_GenesisEndMarker'(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:21:9+118, instance <timestamp::CurrentTimeMicroseconds>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'$1_timestamp_CurrentTimeMicroseconds'($1_from_bcs_deserialize'$1_timestamp_CurrentTimeMicroseconds'(b1), $1_from_bcs_deserialize'$1_timestamp_CurrentTimeMicroseconds'(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:21:9+118, instance <simple_map::SimpleMap<u64, vector<u8>>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'$1_simple_map_SimpleMap'u64_vec'u8'''($1_from_bcs_deserialize'$1_simple_map_SimpleMap'u64_vec'u8'''(b1), $1_from_bcs_deserialize'$1_simple_map_SimpleMap'u64_vec'u8'''(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:21:9+118, instance <simple_map::SimpleMap<address, account::SignerCapability>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'$1_simple_map_SimpleMap'address_$1_account_SignerCapability''($1_from_bcs_deserialize'$1_simple_map_SimpleMap'address_$1_account_SignerCapability''(b1), $1_from_bcs_deserialize'$1_simple_map_SimpleMap'address_$1_account_SignerCapability''(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:21:9+118, instance <simple_map::SimpleMap<string::String, vector<u8>>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'$1_simple_map_SimpleMap'$1_string_String_vec'u8'''($1_from_bcs_deserialize'$1_simple_map_SimpleMap'$1_string_String_vec'u8'''(b1), $1_from_bcs_deserialize'$1_simple_map_SimpleMap'$1_string_String_vec'u8'''(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:21:9+118, instance <voting::Proposal<governance_proposal::GovernanceProposal>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'$1_voting_Proposal'$1_governance_proposal_GovernanceProposal''($1_from_bcs_deserialize'$1_voting_Proposal'$1_governance_proposal_GovernanceProposal''(b1), $1_from_bcs_deserialize'$1_voting_Proposal'$1_governance_proposal_GovernanceProposal''(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:21:9+118, instance <voting::ResolveProposal>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'$1_voting_ResolveProposal'($1_from_bcs_deserialize'$1_voting_ResolveProposal'(b1), $1_from_bcs_deserialize'$1_voting_ResolveProposal'(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:21:9+118, instance <voting::VotingEvents>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'$1_voting_VotingEvents'($1_from_bcs_deserialize'$1_voting_VotingEvents'(b1), $1_from_bcs_deserialize'$1_voting_VotingEvents'(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:21:9+118, instance <voting::VotingForum<governance_proposal::GovernanceProposal>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'$1_voting_VotingForum'$1_governance_proposal_GovernanceProposal''($1_from_bcs_deserialize'$1_voting_VotingForum'$1_governance_proposal_GovernanceProposal''(b1), $1_from_bcs_deserialize'$1_voting_VotingForum'$1_governance_proposal_GovernanceProposal''(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:21:9+118, instance <staking_config::StakingConfig>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'$1_staking_config_StakingConfig'($1_from_bcs_deserialize'$1_staking_config_StakingConfig'(b1), $1_from_bcs_deserialize'$1_staking_config_StakingConfig'(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:21:9+118, instance <stake::AptosCoinCapabilities>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'$1_stake_AptosCoinCapabilities'($1_from_bcs_deserialize'$1_stake_AptosCoinCapabilities'(b1), $1_from_bcs_deserialize'$1_stake_AptosCoinCapabilities'(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:21:9+118, instance <stake::ValidatorConfig>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'$1_stake_ValidatorConfig'($1_from_bcs_deserialize'$1_stake_ValidatorConfig'(b1), $1_from_bcs_deserialize'$1_stake_ValidatorConfig'(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:21:9+118, instance <stake::ValidatorPerformance>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'$1_stake_ValidatorPerformance'($1_from_bcs_deserialize'$1_stake_ValidatorPerformance'(b1), $1_from_bcs_deserialize'$1_stake_ValidatorPerformance'(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:21:9+118, instance <stake::ValidatorSet>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'$1_stake_ValidatorSet'($1_from_bcs_deserialize'$1_stake_ValidatorSet'(b1), $1_from_bcs_deserialize'$1_stake_ValidatorSet'(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:21:9+118, instance <transaction_fee::AptosCoinCapabilities>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'$1_transaction_fee_AptosCoinCapabilities'($1_from_bcs_deserialize'$1_transaction_fee_AptosCoinCapabilities'(b1), $1_from_bcs_deserialize'$1_transaction_fee_AptosCoinCapabilities'(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:21:9+118, instance <state_storage::GasParameter>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'$1_state_storage_GasParameter'($1_from_bcs_deserialize'$1_state_storage_GasParameter'(b1), $1_from_bcs_deserialize'$1_state_storage_GasParameter'(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:21:9+118, instance <state_storage::StateStorageUsage>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'$1_state_storage_StateStorageUsage'($1_from_bcs_deserialize'$1_state_storage_StateStorageUsage'(b1), $1_from_bcs_deserialize'$1_state_storage_StateStorageUsage'(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:21:9+118, instance <state_storage::Usage>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'$1_state_storage_Usage'($1_from_bcs_deserialize'$1_state_storage_Usage'(b1), $1_from_bcs_deserialize'$1_state_storage_Usage'(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:21:9+118, instance <storage_gas::GasCurve>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'$1_storage_gas_GasCurve'($1_from_bcs_deserialize'$1_storage_gas_GasCurve'(b1), $1_from_bcs_deserialize'$1_storage_gas_GasCurve'(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:21:9+118, instance <storage_gas::Point>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'$1_storage_gas_Point'($1_from_bcs_deserialize'$1_storage_gas_Point'(b1), $1_from_bcs_deserialize'$1_storage_gas_Point'(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:21:9+118, instance <storage_gas::StorageGas>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'$1_storage_gas_StorageGas'($1_from_bcs_deserialize'$1_storage_gas_StorageGas'(b1), $1_from_bcs_deserialize'$1_storage_gas_StorageGas'(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:21:9+118, instance <storage_gas::StorageGasConfig>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'$1_storage_gas_StorageGasConfig'($1_from_bcs_deserialize'$1_storage_gas_StorageGasConfig'(b1), $1_from_bcs_deserialize'$1_storage_gas_StorageGasConfig'(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:21:9+118, instance <storage_gas::UsageGasConfig>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'$1_storage_gas_UsageGasConfig'($1_from_bcs_deserialize'$1_storage_gas_UsageGasConfig'(b1), $1_from_bcs_deserialize'$1_storage_gas_UsageGasConfig'(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:21:9+118, instance <reconfiguration::Configuration>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'$1_reconfiguration_Configuration'($1_from_bcs_deserialize'$1_reconfiguration_Configuration'(b1), $1_from_bcs_deserialize'$1_reconfiguration_Configuration'(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:21:9+118, instance <governance_proposal::GovernanceProposal>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'$1_governance_proposal_GovernanceProposal'($1_from_bcs_deserialize'$1_governance_proposal_GovernanceProposal'(b1), $1_from_bcs_deserialize'$1_governance_proposal_GovernanceProposal'(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:21:9+118, instance <aptos_governance::ApprovedExecutionHashes>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'$1_aptos_governance_ApprovedExecutionHashes'($1_from_bcs_deserialize'$1_aptos_governance_ApprovedExecutionHashes'(b1), $1_from_bcs_deserialize'$1_aptos_governance_ApprovedExecutionHashes'(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:21:9+118, instance <aptos_governance::GovernanceResponsbility>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'$1_aptos_governance_GovernanceResponsbility'($1_from_bcs_deserialize'$1_aptos_governance_GovernanceResponsbility'(b1), $1_from_bcs_deserialize'$1_aptos_governance_GovernanceResponsbility'(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:21:9+118, instance <block::BlockResource>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'$1_block_BlockResource'($1_from_bcs_deserialize'$1_block_BlockResource'(b1), $1_from_bcs_deserialize'$1_block_BlockResource'(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:21:9+118, instance <#0>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'#0'($1_from_bcs_deserialize'#0'(b1), $1_from_bcs_deserialize'#0'(b2)))));

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/../move-stdlib/sources/vector.move:143:5+86
function {:inline} $1_vector_$is_empty'u128'(v: Vec (int)): bool {
    $IsEqual'u64'($1_vector_$length'u128'(v), 0)
}

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/../move-stdlib/sources/option.move:69:10+91
function {:inline} $1_option_spec_is_none'u128'(t: $1_option_Option'u128'): bool {
    $1_vector_$is_empty'u128'($vec#$1_option_Option'u128'(t))
}

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/../move-stdlib/sources/option.move:82:10+92
function {:inline} $1_option_spec_is_some'u128'(t: $1_option_Option'u128'): bool {
    !$1_vector_$is_empty'u128'($vec#$1_option_Option'u128'(t))
}

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/../move-stdlib/sources/option.move:111:10+78
function {:inline} $1_option_spec_borrow'u128'(t: $1_option_Option'u128'): int {
    ReadVec($vec#$1_option_Option'u128'(t), 0)
}

// struct option::Option<u128> at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/../move-stdlib/sources/option.move:7:5+81
type {:datatype} $1_option_Option'u128';
function {:constructor} $1_option_Option'u128'($vec: Vec (int)): $1_option_Option'u128';
function {:inline} $Update'$1_option_Option'u128''_vec(s: $1_option_Option'u128', x: Vec (int)): $1_option_Option'u128' {
    $1_option_Option'u128'(x)
}
function $IsValid'$1_option_Option'u128''(s: $1_option_Option'u128'): bool {
    $IsValid'vec'u128''($vec#$1_option_Option'u128'(s))
}
function {:inline} $IsEqual'$1_option_Option'u128''(s1: $1_option_Option'u128', s2: $1_option_Option'u128'): bool {
    $IsEqual'vec'u128''($vec#$1_option_Option'u128'(s1), $vec#$1_option_Option'u128'(s2))}

// struct option::Option<governance_proposal::GovernanceProposal> at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/../move-stdlib/sources/option.move:7:5+81
type {:datatype} $1_option_Option'$1_governance_proposal_GovernanceProposal';
function {:constructor} $1_option_Option'$1_governance_proposal_GovernanceProposal'($vec: Vec ($1_governance_proposal_GovernanceProposal)): $1_option_Option'$1_governance_proposal_GovernanceProposal';
function {:inline} $Update'$1_option_Option'$1_governance_proposal_GovernanceProposal''_vec(s: $1_option_Option'$1_governance_proposal_GovernanceProposal', x: Vec ($1_governance_proposal_GovernanceProposal)): $1_option_Option'$1_governance_proposal_GovernanceProposal' {
    $1_option_Option'$1_governance_proposal_GovernanceProposal'(x)
}
function $IsValid'$1_option_Option'$1_governance_proposal_GovernanceProposal''(s: $1_option_Option'$1_governance_proposal_GovernanceProposal'): bool {
    $IsValid'vec'$1_governance_proposal_GovernanceProposal''($vec#$1_option_Option'$1_governance_proposal_GovernanceProposal'(s))
}
function {:inline} $IsEqual'$1_option_Option'$1_governance_proposal_GovernanceProposal''(s1: $1_option_Option'$1_governance_proposal_GovernanceProposal', s2: $1_option_Option'$1_governance_proposal_GovernanceProposal'): bool {
    $IsEqual'vec'$1_governance_proposal_GovernanceProposal''($vec#$1_option_Option'$1_governance_proposal_GovernanceProposal'(s1), $vec#$1_option_Option'$1_governance_proposal_GovernanceProposal'(s2))}

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/../move-stdlib/sources/string.move:18:5+133
function {:inline} $1_string_$utf8(bytes: Vec (int)): $1_string_String {
    $1_string_String(bytes)
}

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/../move-stdlib/sources/string.spec.move:28:9+50
function  $1_string_spec_internal_check_utf8(v: Vec (int)): bool;
axiom (forall v: Vec (int) ::
(var $$res := $1_string_spec_internal_check_utf8(v);
$IsValid'bool'($$res)));

// struct string::String at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/../move-stdlib/sources/string.move:13:5+70
type {:datatype} $1_string_String;
function {:constructor} $1_string_String($bytes: Vec (int)): $1_string_String;
function {:inline} $Update'$1_string_String'_bytes(s: $1_string_String, x: Vec (int)): $1_string_String {
    $1_string_String(x)
}
function $IsValid'$1_string_String'(s: $1_string_String): bool {
    $IsValid'vec'u8''($bytes#$1_string_String(s))
}
function {:inline} $IsEqual'$1_string_String'(s1: $1_string_String, s2: $1_string_String): bool {
    $IsEqual'vec'u8''($bytes#$1_string_String(s1), $bytes#$1_string_String(s2))}

// fun string::utf8 [baseline] at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/../move-stdlib/sources/string.move:18:5+133
procedure {:inline 1} $1_string_utf8(_$t0: Vec (int)) returns ($ret0: $1_string_String)
{
    // declare local variables
    var $t1: bool;
    var $t2: int;
    var $t3: $1_string_String;
    var $t0: Vec (int);
    var $temp_0'$1_string_String': $1_string_String;
    var $temp_0'vec'u8'': Vec (int);
    $t0 := _$t0;

    // bytecode translation starts here
    // trace_local[bytes]($t0) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/../move-stdlib/sources/string.move:18:5+1
    assume {:print "$at(15,573,574)"} true;
    assume {:print "$track_local(2,13,0):", $t0} $t0 == $t0;

    // $t1 := opaque begin: string::internal_check_utf8($t0) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/../move-stdlib/sources/string.move:19:17+27
    assume {:print "$at(15,634,661)"} true;

    // assume WellFormed($t1) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/../move-stdlib/sources/string.move:19:17+27
    assume $IsValid'bool'($t1);

    // assume Eq<bool>($t1, string::spec_internal_check_utf8($t0)) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/../move-stdlib/sources/string.move:19:17+27
    assume $IsEqual'bool'($t1, $1_string_spec_internal_check_utf8($t0));

    // $t1 := opaque end: string::internal_check_utf8($t0) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/../move-stdlib/sources/string.move:19:17+27

    // if ($t1) goto L1 else goto L0 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/../move-stdlib/sources/string.move:19:9+51
    if ($t1) { goto L1; } else { goto L0; }

    // label L1 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/../move-stdlib/sources/string.move:19:9+51
L1:

    // goto L2 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/../move-stdlib/sources/string.move:19:9+51
    assume {:print "$at(15,626,677)"} true;
    goto L2;

    // label L0 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/../move-stdlib/sources/string.move:19:46+13
L0:

    // $t2 := 1 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/../move-stdlib/sources/string.move:19:46+13
    assume {:print "$at(15,663,676)"} true;
    $t2 := 1;
    assume $IsValid'u64'($t2);

    // trace_abort($t2) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/../move-stdlib/sources/string.move:19:9+51
    assume {:print "$at(15,626,677)"} true;
    assume {:print "$track_abort(2,13):", $t2} $t2 == $t2;

    // goto L4 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/../move-stdlib/sources/string.move:19:9+51
    goto L4;

    // label L2 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/../move-stdlib/sources/string.move:20:16+5
    assume {:print "$at(15,694,699)"} true;
L2:

    // $t3 := pack string::String($t0) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/../move-stdlib/sources/string.move:20:9+13
    assume {:print "$at(15,687,700)"} true;
    $t3 := $1_string_String($t0);

    // trace_return[0]($t3) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/../move-stdlib/sources/string.move:20:9+13
    assume {:print "$track_return(2,13,0):", $t3} $t3 == $t3;

    // label L3 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/../move-stdlib/sources/string.move:21:5+1
    assume {:print "$at(15,705,706)"} true;
L3:

    // return $t3 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/../move-stdlib/sources/string.move:21:5+1
    assume {:print "$at(15,705,706)"} true;
    $ret0 := $t3;
    return;

    // label L4 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/../move-stdlib/sources/string.move:21:5+1
L4:

    // abort($t2) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/../move-stdlib/sources/string.move:21:5+1
    assume {:print "$at(15,705,706)"} true;
    $abort_code := $t2;
    $abort_flag := true;
    return;

}

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/../move-stdlib/sources/signer.move:12:5+77
function {:inline} $1_signer_$address_of(s: $signer): int {
    $1_signer_$borrow_address(s)
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

// struct type_info::TypeInfo at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/type_info.move:17:5+145
type {:datatype} $1_type_info_TypeInfo;
function {:constructor} $1_type_info_TypeInfo($account_address: int, $module_name: Vec (int), $struct_name: Vec (int)): $1_type_info_TypeInfo;
function {:inline} $Update'$1_type_info_TypeInfo'_account_address(s: $1_type_info_TypeInfo, x: int): $1_type_info_TypeInfo {
    $1_type_info_TypeInfo(x, $module_name#$1_type_info_TypeInfo(s), $struct_name#$1_type_info_TypeInfo(s))
}
function {:inline} $Update'$1_type_info_TypeInfo'_module_name(s: $1_type_info_TypeInfo, x: Vec (int)): $1_type_info_TypeInfo {
    $1_type_info_TypeInfo($account_address#$1_type_info_TypeInfo(s), x, $struct_name#$1_type_info_TypeInfo(s))
}
function {:inline} $Update'$1_type_info_TypeInfo'_struct_name(s: $1_type_info_TypeInfo, x: Vec (int)): $1_type_info_TypeInfo {
    $1_type_info_TypeInfo($account_address#$1_type_info_TypeInfo(s), $module_name#$1_type_info_TypeInfo(s), x)
}
function $IsValid'$1_type_info_TypeInfo'(s: $1_type_info_TypeInfo): bool {
    $IsValid'address'($account_address#$1_type_info_TypeInfo(s))
      && $IsValid'vec'u8''($module_name#$1_type_info_TypeInfo(s))
      && $IsValid'vec'u8''($struct_name#$1_type_info_TypeInfo(s))
}
function {:inline} $IsEqual'$1_type_info_TypeInfo'(s1: $1_type_info_TypeInfo, s2: $1_type_info_TypeInfo): bool {
    $IsEqual'address'($account_address#$1_type_info_TypeInfo(s1), $account_address#$1_type_info_TypeInfo(s2))
    && $IsEqual'vec'u8''($module_name#$1_type_info_TypeInfo(s1), $module_name#$1_type_info_TypeInfo(s2))
    && $IsEqual'vec'u8''($struct_name#$1_type_info_TypeInfo(s1), $struct_name#$1_type_info_TypeInfo(s2))}

// struct guid::GUID at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/guid.move:7:5+50
type {:datatype} $1_guid_GUID;
function {:constructor} $1_guid_GUID($id: $1_guid_ID): $1_guid_GUID;
function {:inline} $Update'$1_guid_GUID'_id(s: $1_guid_GUID, x: $1_guid_ID): $1_guid_GUID {
    $1_guid_GUID(x)
}
function $IsValid'$1_guid_GUID'(s: $1_guid_GUID): bool {
    $IsValid'$1_guid_ID'($id#$1_guid_GUID(s))
}
function {:inline} $IsEqual'$1_guid_GUID'(s1: $1_guid_GUID, s2: $1_guid_GUID): bool {
    s1 == s2
}

// struct guid::ID at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/guid.move:12:5+209
type {:datatype} $1_guid_ID;
function {:constructor} $1_guid_ID($creation_num: int, $addr: int): $1_guid_ID;
function {:inline} $Update'$1_guid_ID'_creation_num(s: $1_guid_ID, x: int): $1_guid_ID {
    $1_guid_ID(x, $addr#$1_guid_ID(s))
}
function {:inline} $Update'$1_guid_ID'_addr(s: $1_guid_ID, x: int): $1_guid_ID {
    $1_guid_ID($creation_num#$1_guid_ID(s), x)
}
function $IsValid'$1_guid_ID'(s: $1_guid_ID): bool {
    $IsValid'u64'($creation_num#$1_guid_ID(s))
      && $IsValid'address'($addr#$1_guid_ID(s))
}
function {:inline} $IsEqual'$1_guid_ID'(s1: $1_guid_ID, s2: $1_guid_ID): bool {
    s1 == s2
}

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:7:9+41
function  $1_from_bcs_deserialize'bool'(bytes: Vec (int)): bool;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserialize'bool'(bytes);
$IsValid'bool'($$res)));

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:7:9+41
function  $1_from_bcs_deserialize'u8'(bytes: Vec (int)): int;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserialize'u8'(bytes);
$IsValid'u8'($$res)));

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
function  $1_from_bcs_deserialize'signer'(bytes: Vec (int)): $signer;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserialize'signer'(bytes);
$IsValid'signer'($$res)));

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:7:9+41
function  $1_from_bcs_deserialize'vec'u8''(bytes: Vec (int)): Vec (int);
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserialize'vec'u8''(bytes);
$IsValid'vec'u8''($$res)));

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:7:9+41
function  $1_from_bcs_deserialize'vec'u64''(bytes: Vec (int)): Vec (int);
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserialize'vec'u64''(bytes);
$IsValid'vec'u64''($$res)));

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:7:9+41
function  $1_from_bcs_deserialize'vec'u128''(bytes: Vec (int)): Vec (int);
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserialize'vec'u128''(bytes);
$IsValid'vec'u128''($$res)));

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:7:9+41
function  $1_from_bcs_deserialize'vec'$1_stake_IndividualValidatorPerformance''(bytes: Vec (int)): Vec ($1_stake_IndividualValidatorPerformance);
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserialize'vec'$1_stake_IndividualValidatorPerformance''(bytes);
$IsValid'vec'$1_stake_IndividualValidatorPerformance''($$res)));

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:7:9+41
function  $1_from_bcs_deserialize'vec'$1_stake_ValidatorInfo''(bytes: Vec (int)): Vec ($1_stake_ValidatorInfo);
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserialize'vec'$1_stake_ValidatorInfo''(bytes);
$IsValid'vec'$1_stake_ValidatorInfo''($$res)));

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:7:9+41
function  $1_from_bcs_deserialize'vec'$1_storage_gas_Point''(bytes: Vec (int)): Vec ($1_storage_gas_Point);
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserialize'vec'$1_storage_gas_Point''(bytes);
$IsValid'vec'$1_storage_gas_Point''($$res)));

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:7:9+41
function  $1_from_bcs_deserialize'vec'$1_governance_proposal_GovernanceProposal''(bytes: Vec (int)): Vec ($1_governance_proposal_GovernanceProposal);
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserialize'vec'$1_governance_proposal_GovernanceProposal''(bytes);
$IsValid'vec'$1_governance_proposal_GovernanceProposal''($$res)));

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:7:9+41
function  $1_from_bcs_deserialize'vec'#0''(bytes: Vec (int)): Vec (#0);
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserialize'vec'#0''(bytes);
$IsValid'vec'#0''($$res)));

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:7:9+41
function  $1_from_bcs_deserialize'$1_option_Option'u128''(bytes: Vec (int)): $1_option_Option'u128';
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserialize'$1_option_Option'u128''(bytes);
$IsValid'$1_option_Option'u128''($$res)));

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:7:9+41
function  $1_from_bcs_deserialize'$1_option_Option'$1_governance_proposal_GovernanceProposal''(bytes: Vec (int)): $1_option_Option'$1_governance_proposal_GovernanceProposal';
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserialize'$1_option_Option'$1_governance_proposal_GovernanceProposal''(bytes);
$IsValid'$1_option_Option'$1_governance_proposal_GovernanceProposal''($$res)));

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:7:9+41
function  $1_from_bcs_deserialize'$1_string_String'(bytes: Vec (int)): $1_string_String;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserialize'$1_string_String'(bytes);
$IsValid'$1_string_String'($$res)));

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:7:9+41
function  $1_from_bcs_deserialize'$1_type_info_TypeInfo'(bytes: Vec (int)): $1_type_info_TypeInfo;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserialize'$1_type_info_TypeInfo'(bytes);
$IsValid'$1_type_info_TypeInfo'($$res)));

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:7:9+41
function  $1_from_bcs_deserialize'$1_table_Table'u64_$1_voting_Proposal'$1_governance_proposal_GovernanceProposal'''(bytes: Vec (int)): Table int ($1_voting_Proposal'$1_governance_proposal_GovernanceProposal');
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserialize'$1_table_Table'u64_$1_voting_Proposal'$1_governance_proposal_GovernanceProposal'''(bytes);
$IsValid'$1_table_Table'u64_$1_voting_Proposal'$1_governance_proposal_GovernanceProposal'''($$res)));

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:7:9+41
function  $1_from_bcs_deserialize'$1_guid_GUID'(bytes: Vec (int)): $1_guid_GUID;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserialize'$1_guid_GUID'(bytes);
$IsValid'$1_guid_GUID'($$res)));

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:7:9+41
function  $1_from_bcs_deserialize'$1_guid_ID'(bytes: Vec (int)): $1_guid_ID;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserialize'$1_guid_ID'(bytes);
$IsValid'$1_guid_ID'($$res)));

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:7:9+41
function  $1_from_bcs_deserialize'$1_event_EventHandle'$1_voting_CreateProposalEvent''(bytes: Vec (int)): $1_event_EventHandle'$1_voting_CreateProposalEvent';
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserialize'$1_event_EventHandle'$1_voting_CreateProposalEvent''(bytes);
$IsValid'$1_event_EventHandle'$1_voting_CreateProposalEvent''($$res)));

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:7:9+41
function  $1_from_bcs_deserialize'$1_event_EventHandle'$1_voting_RegisterForumEvent''(bytes: Vec (int)): $1_event_EventHandle'$1_voting_RegisterForumEvent';
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserialize'$1_event_EventHandle'$1_voting_RegisterForumEvent''(bytes);
$IsValid'$1_event_EventHandle'$1_voting_RegisterForumEvent''($$res)));

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:7:9+41
function  $1_from_bcs_deserialize'$1_event_EventHandle'$1_voting_ResolveProposal''(bytes: Vec (int)): $1_event_EventHandle'$1_voting_ResolveProposal';
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserialize'$1_event_EventHandle'$1_voting_ResolveProposal''(bytes);
$IsValid'$1_event_EventHandle'$1_voting_ResolveProposal''($$res)));

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:7:9+41
function  $1_from_bcs_deserialize'$1_event_EventHandle'$1_voting_VoteEvent''(bytes: Vec (int)): $1_event_EventHandle'$1_voting_VoteEvent';
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserialize'$1_event_EventHandle'$1_voting_VoteEvent''(bytes);
$IsValid'$1_event_EventHandle'$1_voting_VoteEvent''($$res)));

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:7:9+41
function  $1_from_bcs_deserialize'$1_event_EventHandle'$1_reconfiguration_NewEpochEvent''(bytes: Vec (int)): $1_event_EventHandle'$1_reconfiguration_NewEpochEvent';
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserialize'$1_event_EventHandle'$1_reconfiguration_NewEpochEvent''(bytes);
$IsValid'$1_event_EventHandle'$1_reconfiguration_NewEpochEvent''($$res)));

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:7:9+41
function  $1_from_bcs_deserialize'$1_event_EventHandle'$1_block_NewBlockEvent''(bytes: Vec (int)): $1_event_EventHandle'$1_block_NewBlockEvent';
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserialize'$1_event_EventHandle'$1_block_NewBlockEvent''(bytes);
$IsValid'$1_event_EventHandle'$1_block_NewBlockEvent''($$res)));

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:7:9+41
function  $1_from_bcs_deserialize'$1_event_EventHandle'$1_block_UpdateEpochIntervalEvent''(bytes: Vec (int)): $1_event_EventHandle'$1_block_UpdateEpochIntervalEvent';
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserialize'$1_event_EventHandle'$1_block_UpdateEpochIntervalEvent''(bytes);
$IsValid'$1_event_EventHandle'$1_block_UpdateEpochIntervalEvent''($$res)));

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:7:9+41
function  $1_from_bcs_deserialize'$1_account_SignerCapability'(bytes: Vec (int)): $1_account_SignerCapability;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserialize'$1_account_SignerCapability'(bytes);
$IsValid'$1_account_SignerCapability'($$res)));

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:7:9+41
function  $1_from_bcs_deserialize'$1_coin_BurnCapability'$1_aptos_coin_AptosCoin''(bytes: Vec (int)): $1_coin_BurnCapability'$1_aptos_coin_AptosCoin';
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserialize'$1_coin_BurnCapability'$1_aptos_coin_AptosCoin''(bytes);
$IsValid'$1_coin_BurnCapability'$1_aptos_coin_AptosCoin''($$res)));

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:7:9+41
function  $1_from_bcs_deserialize'$1_coin_MintCapability'$1_aptos_coin_AptosCoin''(bytes: Vec (int)): $1_coin_MintCapability'$1_aptos_coin_AptosCoin';
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserialize'$1_coin_MintCapability'$1_aptos_coin_AptosCoin''(bytes);
$IsValid'$1_coin_MintCapability'$1_aptos_coin_AptosCoin''($$res)));

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:7:9+41
function  $1_from_bcs_deserialize'$1_chain_status_GenesisEndMarker'(bytes: Vec (int)): $1_chain_status_GenesisEndMarker;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserialize'$1_chain_status_GenesisEndMarker'(bytes);
$IsValid'$1_chain_status_GenesisEndMarker'($$res)));

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:7:9+41
function  $1_from_bcs_deserialize'$1_timestamp_CurrentTimeMicroseconds'(bytes: Vec (int)): $1_timestamp_CurrentTimeMicroseconds;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserialize'$1_timestamp_CurrentTimeMicroseconds'(bytes);
$IsValid'$1_timestamp_CurrentTimeMicroseconds'($$res)));

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:7:9+41
function  $1_from_bcs_deserialize'$1_simple_map_SimpleMap'u64_vec'u8'''(bytes: Vec (int)): Table int (Vec (int));
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserialize'$1_simple_map_SimpleMap'u64_vec'u8'''(bytes);
$IsValid'$1_simple_map_SimpleMap'u64_vec'u8'''($$res)));

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:7:9+41
function  $1_from_bcs_deserialize'$1_simple_map_SimpleMap'address_$1_account_SignerCapability''(bytes: Vec (int)): Table int ($1_account_SignerCapability);
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserialize'$1_simple_map_SimpleMap'address_$1_account_SignerCapability''(bytes);
$IsValid'$1_simple_map_SimpleMap'address_$1_account_SignerCapability''($$res)));

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:7:9+41
function  $1_from_bcs_deserialize'$1_simple_map_SimpleMap'$1_string_String_vec'u8'''(bytes: Vec (int)): Table int (Vec (int));
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserialize'$1_simple_map_SimpleMap'$1_string_String_vec'u8'''(bytes);
$IsValid'$1_simple_map_SimpleMap'$1_string_String_vec'u8'''($$res)));

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:7:9+41
function  $1_from_bcs_deserialize'$1_voting_Proposal'$1_governance_proposal_GovernanceProposal''(bytes: Vec (int)): $1_voting_Proposal'$1_governance_proposal_GovernanceProposal';
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserialize'$1_voting_Proposal'$1_governance_proposal_GovernanceProposal''(bytes);
$IsValid'$1_voting_Proposal'$1_governance_proposal_GovernanceProposal''($$res)));

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:7:9+41
function  $1_from_bcs_deserialize'$1_voting_ResolveProposal'(bytes: Vec (int)): $1_voting_ResolveProposal;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserialize'$1_voting_ResolveProposal'(bytes);
$IsValid'$1_voting_ResolveProposal'($$res)));

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:7:9+41
function  $1_from_bcs_deserialize'$1_voting_VotingEvents'(bytes: Vec (int)): $1_voting_VotingEvents;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserialize'$1_voting_VotingEvents'(bytes);
$IsValid'$1_voting_VotingEvents'($$res)));

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:7:9+41
function  $1_from_bcs_deserialize'$1_voting_VotingForum'$1_governance_proposal_GovernanceProposal''(bytes: Vec (int)): $1_voting_VotingForum'$1_governance_proposal_GovernanceProposal';
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserialize'$1_voting_VotingForum'$1_governance_proposal_GovernanceProposal''(bytes);
$IsValid'$1_voting_VotingForum'$1_governance_proposal_GovernanceProposal''($$res)));

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:7:9+41
function  $1_from_bcs_deserialize'$1_staking_config_StakingConfig'(bytes: Vec (int)): $1_staking_config_StakingConfig;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserialize'$1_staking_config_StakingConfig'(bytes);
$IsValid'$1_staking_config_StakingConfig'($$res)));

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:7:9+41
function  $1_from_bcs_deserialize'$1_stake_AptosCoinCapabilities'(bytes: Vec (int)): $1_stake_AptosCoinCapabilities;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserialize'$1_stake_AptosCoinCapabilities'(bytes);
$IsValid'$1_stake_AptosCoinCapabilities'($$res)));

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:7:9+41
function  $1_from_bcs_deserialize'$1_stake_ValidatorConfig'(bytes: Vec (int)): $1_stake_ValidatorConfig;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserialize'$1_stake_ValidatorConfig'(bytes);
$IsValid'$1_stake_ValidatorConfig'($$res)));

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:7:9+41
function  $1_from_bcs_deserialize'$1_stake_ValidatorPerformance'(bytes: Vec (int)): $1_stake_ValidatorPerformance;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserialize'$1_stake_ValidatorPerformance'(bytes);
$IsValid'$1_stake_ValidatorPerformance'($$res)));

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:7:9+41
function  $1_from_bcs_deserialize'$1_stake_ValidatorSet'(bytes: Vec (int)): $1_stake_ValidatorSet;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserialize'$1_stake_ValidatorSet'(bytes);
$IsValid'$1_stake_ValidatorSet'($$res)));

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:7:9+41
function  $1_from_bcs_deserialize'$1_transaction_fee_AptosCoinCapabilities'(bytes: Vec (int)): $1_transaction_fee_AptosCoinCapabilities;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserialize'$1_transaction_fee_AptosCoinCapabilities'(bytes);
$IsValid'$1_transaction_fee_AptosCoinCapabilities'($$res)));

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:7:9+41
function  $1_from_bcs_deserialize'$1_state_storage_GasParameter'(bytes: Vec (int)): $1_state_storage_GasParameter;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserialize'$1_state_storage_GasParameter'(bytes);
$IsValid'$1_state_storage_GasParameter'($$res)));

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:7:9+41
function  $1_from_bcs_deserialize'$1_state_storage_StateStorageUsage'(bytes: Vec (int)): $1_state_storage_StateStorageUsage;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserialize'$1_state_storage_StateStorageUsage'(bytes);
$IsValid'$1_state_storage_StateStorageUsage'($$res)));

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:7:9+41
function  $1_from_bcs_deserialize'$1_state_storage_Usage'(bytes: Vec (int)): $1_state_storage_Usage;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserialize'$1_state_storage_Usage'(bytes);
$IsValid'$1_state_storage_Usage'($$res)));

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:7:9+41
function  $1_from_bcs_deserialize'$1_storage_gas_GasCurve'(bytes: Vec (int)): $1_storage_gas_GasCurve;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserialize'$1_storage_gas_GasCurve'(bytes);
$IsValid'$1_storage_gas_GasCurve'($$res)));

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:7:9+41
function  $1_from_bcs_deserialize'$1_storage_gas_Point'(bytes: Vec (int)): $1_storage_gas_Point;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserialize'$1_storage_gas_Point'(bytes);
$IsValid'$1_storage_gas_Point'($$res)));

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:7:9+41
function  $1_from_bcs_deserialize'$1_storage_gas_StorageGas'(bytes: Vec (int)): $1_storage_gas_StorageGas;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserialize'$1_storage_gas_StorageGas'(bytes);
$IsValid'$1_storage_gas_StorageGas'($$res)));

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:7:9+41
function  $1_from_bcs_deserialize'$1_storage_gas_StorageGasConfig'(bytes: Vec (int)): $1_storage_gas_StorageGasConfig;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserialize'$1_storage_gas_StorageGasConfig'(bytes);
$IsValid'$1_storage_gas_StorageGasConfig'($$res)));

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:7:9+41
function  $1_from_bcs_deserialize'$1_storage_gas_UsageGasConfig'(bytes: Vec (int)): $1_storage_gas_UsageGasConfig;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserialize'$1_storage_gas_UsageGasConfig'(bytes);
$IsValid'$1_storage_gas_UsageGasConfig'($$res)));

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:7:9+41
function  $1_from_bcs_deserialize'$1_reconfiguration_Configuration'(bytes: Vec (int)): $1_reconfiguration_Configuration;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserialize'$1_reconfiguration_Configuration'(bytes);
$IsValid'$1_reconfiguration_Configuration'($$res)));

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:7:9+41
function  $1_from_bcs_deserialize'$1_governance_proposal_GovernanceProposal'(bytes: Vec (int)): $1_governance_proposal_GovernanceProposal;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserialize'$1_governance_proposal_GovernanceProposal'(bytes);
$IsValid'$1_governance_proposal_GovernanceProposal'($$res)));

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:7:9+41
function  $1_from_bcs_deserialize'$1_aptos_governance_ApprovedExecutionHashes'(bytes: Vec (int)): $1_aptos_governance_ApprovedExecutionHashes;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserialize'$1_aptos_governance_ApprovedExecutionHashes'(bytes);
$IsValid'$1_aptos_governance_ApprovedExecutionHashes'($$res)));

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:7:9+41
function  $1_from_bcs_deserialize'$1_aptos_governance_GovernanceResponsbility'(bytes: Vec (int)): $1_aptos_governance_GovernanceResponsbility;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserialize'$1_aptos_governance_GovernanceResponsbility'(bytes);
$IsValid'$1_aptos_governance_GovernanceResponsbility'($$res)));

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:7:9+41
function  $1_from_bcs_deserialize'$1_block_BlockResource'(bytes: Vec (int)): $1_block_BlockResource;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserialize'$1_block_BlockResource'(bytes);
$IsValid'$1_block_BlockResource'($$res)));

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
function  $1_from_bcs_deserializable'u8'(bytes: Vec (int)): bool;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserializable'u8'(bytes);
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
function  $1_from_bcs_deserializable'signer'(bytes: Vec (int)): bool;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserializable'signer'(bytes);
$IsValid'bool'($$res)));

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:11:9+47
function  $1_from_bcs_deserializable'vec'u8''(bytes: Vec (int)): bool;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserializable'vec'u8''(bytes);
$IsValid'bool'($$res)));

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:11:9+47
function  $1_from_bcs_deserializable'vec'u64''(bytes: Vec (int)): bool;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserializable'vec'u64''(bytes);
$IsValid'bool'($$res)));

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:11:9+47
function  $1_from_bcs_deserializable'vec'u128''(bytes: Vec (int)): bool;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserializable'vec'u128''(bytes);
$IsValid'bool'($$res)));

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:11:9+47
function  $1_from_bcs_deserializable'vec'$1_stake_IndividualValidatorPerformance''(bytes: Vec (int)): bool;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserializable'vec'$1_stake_IndividualValidatorPerformance''(bytes);
$IsValid'bool'($$res)));

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:11:9+47
function  $1_from_bcs_deserializable'vec'$1_stake_ValidatorInfo''(bytes: Vec (int)): bool;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserializable'vec'$1_stake_ValidatorInfo''(bytes);
$IsValid'bool'($$res)));

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:11:9+47
function  $1_from_bcs_deserializable'vec'$1_storage_gas_Point''(bytes: Vec (int)): bool;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserializable'vec'$1_storage_gas_Point''(bytes);
$IsValid'bool'($$res)));

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:11:9+47
function  $1_from_bcs_deserializable'vec'$1_governance_proposal_GovernanceProposal''(bytes: Vec (int)): bool;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserializable'vec'$1_governance_proposal_GovernanceProposal''(bytes);
$IsValid'bool'($$res)));

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:11:9+47
function  $1_from_bcs_deserializable'vec'#0''(bytes: Vec (int)): bool;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserializable'vec'#0''(bytes);
$IsValid'bool'($$res)));

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:11:9+47
function  $1_from_bcs_deserializable'$1_option_Option'u128''(bytes: Vec (int)): bool;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserializable'$1_option_Option'u128''(bytes);
$IsValid'bool'($$res)));

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:11:9+47
function  $1_from_bcs_deserializable'$1_option_Option'$1_governance_proposal_GovernanceProposal''(bytes: Vec (int)): bool;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserializable'$1_option_Option'$1_governance_proposal_GovernanceProposal''(bytes);
$IsValid'bool'($$res)));

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:11:9+47
function  $1_from_bcs_deserializable'$1_string_String'(bytes: Vec (int)): bool;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserializable'$1_string_String'(bytes);
$IsValid'bool'($$res)));

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:11:9+47
function  $1_from_bcs_deserializable'$1_type_info_TypeInfo'(bytes: Vec (int)): bool;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserializable'$1_type_info_TypeInfo'(bytes);
$IsValid'bool'($$res)));

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:11:9+47
function  $1_from_bcs_deserializable'$1_table_Table'u64_$1_voting_Proposal'$1_governance_proposal_GovernanceProposal'''(bytes: Vec (int)): bool;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserializable'$1_table_Table'u64_$1_voting_Proposal'$1_governance_proposal_GovernanceProposal'''(bytes);
$IsValid'bool'($$res)));

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:11:9+47
function  $1_from_bcs_deserializable'$1_guid_GUID'(bytes: Vec (int)): bool;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserializable'$1_guid_GUID'(bytes);
$IsValid'bool'($$res)));

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:11:9+47
function  $1_from_bcs_deserializable'$1_guid_ID'(bytes: Vec (int)): bool;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserializable'$1_guid_ID'(bytes);
$IsValid'bool'($$res)));

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:11:9+47
function  $1_from_bcs_deserializable'$1_event_EventHandle'$1_voting_CreateProposalEvent''(bytes: Vec (int)): bool;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserializable'$1_event_EventHandle'$1_voting_CreateProposalEvent''(bytes);
$IsValid'bool'($$res)));

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:11:9+47
function  $1_from_bcs_deserializable'$1_event_EventHandle'$1_voting_RegisterForumEvent''(bytes: Vec (int)): bool;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserializable'$1_event_EventHandle'$1_voting_RegisterForumEvent''(bytes);
$IsValid'bool'($$res)));

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:11:9+47
function  $1_from_bcs_deserializable'$1_event_EventHandle'$1_voting_ResolveProposal''(bytes: Vec (int)): bool;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserializable'$1_event_EventHandle'$1_voting_ResolveProposal''(bytes);
$IsValid'bool'($$res)));

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:11:9+47
function  $1_from_bcs_deserializable'$1_event_EventHandle'$1_voting_VoteEvent''(bytes: Vec (int)): bool;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserializable'$1_event_EventHandle'$1_voting_VoteEvent''(bytes);
$IsValid'bool'($$res)));

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:11:9+47
function  $1_from_bcs_deserializable'$1_event_EventHandle'$1_reconfiguration_NewEpochEvent''(bytes: Vec (int)): bool;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserializable'$1_event_EventHandle'$1_reconfiguration_NewEpochEvent''(bytes);
$IsValid'bool'($$res)));

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:11:9+47
function  $1_from_bcs_deserializable'$1_event_EventHandle'$1_block_NewBlockEvent''(bytes: Vec (int)): bool;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserializable'$1_event_EventHandle'$1_block_NewBlockEvent''(bytes);
$IsValid'bool'($$res)));

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:11:9+47
function  $1_from_bcs_deserializable'$1_event_EventHandle'$1_block_UpdateEpochIntervalEvent''(bytes: Vec (int)): bool;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserializable'$1_event_EventHandle'$1_block_UpdateEpochIntervalEvent''(bytes);
$IsValid'bool'($$res)));

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:11:9+47
function  $1_from_bcs_deserializable'$1_account_SignerCapability'(bytes: Vec (int)): bool;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserializable'$1_account_SignerCapability'(bytes);
$IsValid'bool'($$res)));

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:11:9+47
function  $1_from_bcs_deserializable'$1_coin_BurnCapability'$1_aptos_coin_AptosCoin''(bytes: Vec (int)): bool;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserializable'$1_coin_BurnCapability'$1_aptos_coin_AptosCoin''(bytes);
$IsValid'bool'($$res)));

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:11:9+47
function  $1_from_bcs_deserializable'$1_coin_MintCapability'$1_aptos_coin_AptosCoin''(bytes: Vec (int)): bool;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserializable'$1_coin_MintCapability'$1_aptos_coin_AptosCoin''(bytes);
$IsValid'bool'($$res)));

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:11:9+47
function  $1_from_bcs_deserializable'$1_chain_status_GenesisEndMarker'(bytes: Vec (int)): bool;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserializable'$1_chain_status_GenesisEndMarker'(bytes);
$IsValid'bool'($$res)));

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:11:9+47
function  $1_from_bcs_deserializable'$1_timestamp_CurrentTimeMicroseconds'(bytes: Vec (int)): bool;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserializable'$1_timestamp_CurrentTimeMicroseconds'(bytes);
$IsValid'bool'($$res)));

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:11:9+47
function  $1_from_bcs_deserializable'$1_simple_map_SimpleMap'u64_vec'u8'''(bytes: Vec (int)): bool;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserializable'$1_simple_map_SimpleMap'u64_vec'u8'''(bytes);
$IsValid'bool'($$res)));

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:11:9+47
function  $1_from_bcs_deserializable'$1_simple_map_SimpleMap'address_$1_account_SignerCapability''(bytes: Vec (int)): bool;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserializable'$1_simple_map_SimpleMap'address_$1_account_SignerCapability''(bytes);
$IsValid'bool'($$res)));

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:11:9+47
function  $1_from_bcs_deserializable'$1_simple_map_SimpleMap'$1_string_String_vec'u8'''(bytes: Vec (int)): bool;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserializable'$1_simple_map_SimpleMap'$1_string_String_vec'u8'''(bytes);
$IsValid'bool'($$res)));

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:11:9+47
function  $1_from_bcs_deserializable'$1_voting_Proposal'$1_governance_proposal_GovernanceProposal''(bytes: Vec (int)): bool;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserializable'$1_voting_Proposal'$1_governance_proposal_GovernanceProposal''(bytes);
$IsValid'bool'($$res)));

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:11:9+47
function  $1_from_bcs_deserializable'$1_voting_ResolveProposal'(bytes: Vec (int)): bool;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserializable'$1_voting_ResolveProposal'(bytes);
$IsValid'bool'($$res)));

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:11:9+47
function  $1_from_bcs_deserializable'$1_voting_VotingEvents'(bytes: Vec (int)): bool;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserializable'$1_voting_VotingEvents'(bytes);
$IsValid'bool'($$res)));

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:11:9+47
function  $1_from_bcs_deserializable'$1_voting_VotingForum'$1_governance_proposal_GovernanceProposal''(bytes: Vec (int)): bool;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserializable'$1_voting_VotingForum'$1_governance_proposal_GovernanceProposal''(bytes);
$IsValid'bool'($$res)));

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:11:9+47
function  $1_from_bcs_deserializable'$1_staking_config_StakingConfig'(bytes: Vec (int)): bool;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserializable'$1_staking_config_StakingConfig'(bytes);
$IsValid'bool'($$res)));

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:11:9+47
function  $1_from_bcs_deserializable'$1_stake_AptosCoinCapabilities'(bytes: Vec (int)): bool;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserializable'$1_stake_AptosCoinCapabilities'(bytes);
$IsValid'bool'($$res)));

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:11:9+47
function  $1_from_bcs_deserializable'$1_stake_ValidatorConfig'(bytes: Vec (int)): bool;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserializable'$1_stake_ValidatorConfig'(bytes);
$IsValid'bool'($$res)));

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:11:9+47
function  $1_from_bcs_deserializable'$1_stake_ValidatorPerformance'(bytes: Vec (int)): bool;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserializable'$1_stake_ValidatorPerformance'(bytes);
$IsValid'bool'($$res)));

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:11:9+47
function  $1_from_bcs_deserializable'$1_stake_ValidatorSet'(bytes: Vec (int)): bool;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserializable'$1_stake_ValidatorSet'(bytes);
$IsValid'bool'($$res)));

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:11:9+47
function  $1_from_bcs_deserializable'$1_transaction_fee_AptosCoinCapabilities'(bytes: Vec (int)): bool;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserializable'$1_transaction_fee_AptosCoinCapabilities'(bytes);
$IsValid'bool'($$res)));

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:11:9+47
function  $1_from_bcs_deserializable'$1_state_storage_GasParameter'(bytes: Vec (int)): bool;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserializable'$1_state_storage_GasParameter'(bytes);
$IsValid'bool'($$res)));

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:11:9+47
function  $1_from_bcs_deserializable'$1_state_storage_StateStorageUsage'(bytes: Vec (int)): bool;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserializable'$1_state_storage_StateStorageUsage'(bytes);
$IsValid'bool'($$res)));

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:11:9+47
function  $1_from_bcs_deserializable'$1_state_storage_Usage'(bytes: Vec (int)): bool;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserializable'$1_state_storage_Usage'(bytes);
$IsValid'bool'($$res)));

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:11:9+47
function  $1_from_bcs_deserializable'$1_storage_gas_GasCurve'(bytes: Vec (int)): bool;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserializable'$1_storage_gas_GasCurve'(bytes);
$IsValid'bool'($$res)));

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:11:9+47
function  $1_from_bcs_deserializable'$1_storage_gas_Point'(bytes: Vec (int)): bool;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserializable'$1_storage_gas_Point'(bytes);
$IsValid'bool'($$res)));

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:11:9+47
function  $1_from_bcs_deserializable'$1_storage_gas_StorageGas'(bytes: Vec (int)): bool;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserializable'$1_storage_gas_StorageGas'(bytes);
$IsValid'bool'($$res)));

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:11:9+47
function  $1_from_bcs_deserializable'$1_storage_gas_StorageGasConfig'(bytes: Vec (int)): bool;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserializable'$1_storage_gas_StorageGasConfig'(bytes);
$IsValid'bool'($$res)));

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:11:9+47
function  $1_from_bcs_deserializable'$1_storage_gas_UsageGasConfig'(bytes: Vec (int)): bool;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserializable'$1_storage_gas_UsageGasConfig'(bytes);
$IsValid'bool'($$res)));

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:11:9+47
function  $1_from_bcs_deserializable'$1_reconfiguration_Configuration'(bytes: Vec (int)): bool;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserializable'$1_reconfiguration_Configuration'(bytes);
$IsValid'bool'($$res)));

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:11:9+47
function  $1_from_bcs_deserializable'$1_governance_proposal_GovernanceProposal'(bytes: Vec (int)): bool;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserializable'$1_governance_proposal_GovernanceProposal'(bytes);
$IsValid'bool'($$res)));

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:11:9+47
function  $1_from_bcs_deserializable'$1_aptos_governance_ApprovedExecutionHashes'(bytes: Vec (int)): bool;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserializable'$1_aptos_governance_ApprovedExecutionHashes'(bytes);
$IsValid'bool'($$res)));

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:11:9+47
function  $1_from_bcs_deserializable'$1_aptos_governance_GovernanceResponsbility'(bytes: Vec (int)): bool;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserializable'$1_aptos_governance_GovernanceResponsbility'(bytes);
$IsValid'bool'($$res)));

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:11:9+47
function  $1_from_bcs_deserializable'$1_block_BlockResource'(bytes: Vec (int)): bool;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserializable'$1_block_BlockResource'(bytes);
$IsValid'bool'($$res)));

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:11:9+47
function  $1_from_bcs_deserializable'#0'(bytes: Vec (int)): bool;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserializable'#0'(bytes);
$IsValid'bool'($$res)));

// fun from_bcs::to_bool [baseline] at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.move:19:5+75
procedure {:inline 1} $1_from_bcs_to_bool(_$t0: Vec (int)) returns ($ret0: bool)
{
    // declare local variables
    var $t1: bool;
    var $t2: bool;
    var $t3: int;
    var $t0: Vec (int);
    var $temp_0'bool': bool;
    var $temp_0'vec'u8'': Vec (int);
    $t0 := _$t0;

    // bytecode translation starts here
    // trace_local[v]($t0) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.move:19:5+1
    assume {:print "$at(48,796,797)"} true;
    assume {:print "$track_local(14,2,0):", $t0} $t0 == $t0;

    // $t1 := opaque begin: from_bcs::from_bytes<bool>($t0) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.move:20:9+19
    assume {:print "$at(48,846,865)"} true;

    // assume Identical($t2, Not(from_bcs::deserializable<bool>($t0))) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.move:20:9+19
    assume ($t2 == !$1_from_bcs_deserializable'bool'($t0));

    // if ($t2) goto L4 else goto L3 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.move:20:9+19
    if ($t2) { goto L4; } else { goto L3; }

    // label L4 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.move:20:9+19
L4:

    // trace_abort($t3) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.move:20:9+19
    assume {:print "$at(48,846,865)"} true;
    assume {:print "$track_abort(14,2):", $t3} $t3 == $t3;

    // goto L2 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.move:20:9+19
    goto L2;

    // label L3 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.move:20:9+19
L3:

    // assume WellFormed($t1) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.move:20:9+19
    assume {:print "$at(48,846,865)"} true;
    assume $IsValid'bool'($t1);

    // assume Eq<bool>($t1, from_bcs::deserialize<bool>($t0)) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.move:20:9+19
    assume $IsEqual'bool'($t1, $1_from_bcs_deserialize'bool'($t0));

    // $t1 := opaque end: from_bcs::from_bytes<bool>($t0) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.move:20:9+19

    // trace_return[0]($t1) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.move:20:9+19
    assume {:print "$track_return(14,2,0):", $t1} $t1 == $t1;

    // label L1 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.move:21:5+1
    assume {:print "$at(48,870,871)"} true;
L1:

    // return $t1 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.move:21:5+1
    assume {:print "$at(48,870,871)"} true;
    $ret0 := $t1;
    return;

    // label L2 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.move:21:5+1
L2:

    // abort($t3) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.move:21:5+1
    assume {:print "$at(48,870,871)"} true;
    $abort_code := $t3;
    $abort_flag := true;
    return;

}

// fun from_bcs::to_u64 [baseline] at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.move:35:5+72
procedure {:inline 1} $1_from_bcs_to_u64(_$t0: Vec (int)) returns ($ret0: int)
{
    // declare local variables
    var $t1: int;
    var $t2: bool;
    var $t3: int;
    var $t0: Vec (int);
    var $temp_0'u64': int;
    var $temp_0'vec'u8'': Vec (int);
    $t0 := _$t0;

    // bytecode translation starts here
    // trace_local[v]($t0) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.move:35:5+1
    assume {:print "$at(48,1108,1109)"} true;
    assume {:print "$track_local(14,9,0):", $t0} $t0 == $t0;

    // $t1 := opaque begin: from_bcs::from_bytes<u64>($t0) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.move:36:9+18
    assume {:print "$at(48,1156,1174)"} true;

    // assume Identical($t2, Not(from_bcs::deserializable<u64>($t0))) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.move:36:9+18
    assume ($t2 == !$1_from_bcs_deserializable'u64'($t0));

    // if ($t2) goto L4 else goto L3 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.move:36:9+18
    if ($t2) { goto L4; } else { goto L3; }

    // label L4 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.move:36:9+18
L4:

    // trace_abort($t3) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.move:36:9+18
    assume {:print "$at(48,1156,1174)"} true;
    assume {:print "$track_abort(14,9):", $t3} $t3 == $t3;

    // goto L2 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.move:36:9+18
    goto L2;

    // label L3 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.move:36:9+18
L3:

    // assume WellFormed($t1) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.move:36:9+18
    assume {:print "$at(48,1156,1174)"} true;
    assume $IsValid'u64'($t1);

    // assume Eq<u64>($t1, from_bcs::deserialize<u64>($t0)) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.move:36:9+18
    assume $IsEqual'u64'($t1, $1_from_bcs_deserialize'u64'($t0));

    // $t1 := opaque end: from_bcs::from_bytes<u64>($t0) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.move:36:9+18

    // trace_return[0]($t1) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.move:36:9+18
    assume {:print "$track_return(14,9,0):", $t1} $t1 == $t1;

    // label L1 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.move:37:5+1
    assume {:print "$at(48,1179,1180)"} true;
L1:

    // return $t1 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.move:37:5+1
    assume {:print "$at(48,1179,1180)"} true;
    $ret0 := $t1;
    return;

    // label L2 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.move:37:5+1
L2:

    // abort($t3) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.move:37:5+1
    assume {:print "$at(48,1179,1180)"} true;
    $abort_code := $t3;
    $abort_flag := true;
    return;

}

// struct event::EventHandle<voting::CreateProposalEvent> at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/event.move:16:5+224
type {:datatype} $1_event_EventHandle'$1_voting_CreateProposalEvent';
function {:constructor} $1_event_EventHandle'$1_voting_CreateProposalEvent'($counter: int, $guid: $1_guid_GUID): $1_event_EventHandle'$1_voting_CreateProposalEvent';
function {:inline} $Update'$1_event_EventHandle'$1_voting_CreateProposalEvent''_counter(s: $1_event_EventHandle'$1_voting_CreateProposalEvent', x: int): $1_event_EventHandle'$1_voting_CreateProposalEvent' {
    $1_event_EventHandle'$1_voting_CreateProposalEvent'(x, $guid#$1_event_EventHandle'$1_voting_CreateProposalEvent'(s))
}
function {:inline} $Update'$1_event_EventHandle'$1_voting_CreateProposalEvent''_guid(s: $1_event_EventHandle'$1_voting_CreateProposalEvent', x: $1_guid_GUID): $1_event_EventHandle'$1_voting_CreateProposalEvent' {
    $1_event_EventHandle'$1_voting_CreateProposalEvent'($counter#$1_event_EventHandle'$1_voting_CreateProposalEvent'(s), x)
}
function $IsValid'$1_event_EventHandle'$1_voting_CreateProposalEvent''(s: $1_event_EventHandle'$1_voting_CreateProposalEvent'): bool {
    $IsValid'u64'($counter#$1_event_EventHandle'$1_voting_CreateProposalEvent'(s))
      && $IsValid'$1_guid_GUID'($guid#$1_event_EventHandle'$1_voting_CreateProposalEvent'(s))
}
function {:inline} $IsEqual'$1_event_EventHandle'$1_voting_CreateProposalEvent''(s1: $1_event_EventHandle'$1_voting_CreateProposalEvent', s2: $1_event_EventHandle'$1_voting_CreateProposalEvent'): bool {
    s1 == s2
}

// struct event::EventHandle<voting::RegisterForumEvent> at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/event.move:16:5+224
type {:datatype} $1_event_EventHandle'$1_voting_RegisterForumEvent';
function {:constructor} $1_event_EventHandle'$1_voting_RegisterForumEvent'($counter: int, $guid: $1_guid_GUID): $1_event_EventHandle'$1_voting_RegisterForumEvent';
function {:inline} $Update'$1_event_EventHandle'$1_voting_RegisterForumEvent''_counter(s: $1_event_EventHandle'$1_voting_RegisterForumEvent', x: int): $1_event_EventHandle'$1_voting_RegisterForumEvent' {
    $1_event_EventHandle'$1_voting_RegisterForumEvent'(x, $guid#$1_event_EventHandle'$1_voting_RegisterForumEvent'(s))
}
function {:inline} $Update'$1_event_EventHandle'$1_voting_RegisterForumEvent''_guid(s: $1_event_EventHandle'$1_voting_RegisterForumEvent', x: $1_guid_GUID): $1_event_EventHandle'$1_voting_RegisterForumEvent' {
    $1_event_EventHandle'$1_voting_RegisterForumEvent'($counter#$1_event_EventHandle'$1_voting_RegisterForumEvent'(s), x)
}
function $IsValid'$1_event_EventHandle'$1_voting_RegisterForumEvent''(s: $1_event_EventHandle'$1_voting_RegisterForumEvent'): bool {
    $IsValid'u64'($counter#$1_event_EventHandle'$1_voting_RegisterForumEvent'(s))
      && $IsValid'$1_guid_GUID'($guid#$1_event_EventHandle'$1_voting_RegisterForumEvent'(s))
}
function {:inline} $IsEqual'$1_event_EventHandle'$1_voting_RegisterForumEvent''(s1: $1_event_EventHandle'$1_voting_RegisterForumEvent', s2: $1_event_EventHandle'$1_voting_RegisterForumEvent'): bool {
    s1 == s2
}

// struct event::EventHandle<voting::ResolveProposal> at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/event.move:16:5+224
type {:datatype} $1_event_EventHandle'$1_voting_ResolveProposal';
function {:constructor} $1_event_EventHandle'$1_voting_ResolveProposal'($counter: int, $guid: $1_guid_GUID): $1_event_EventHandle'$1_voting_ResolveProposal';
function {:inline} $Update'$1_event_EventHandle'$1_voting_ResolveProposal''_counter(s: $1_event_EventHandle'$1_voting_ResolveProposal', x: int): $1_event_EventHandle'$1_voting_ResolveProposal' {
    $1_event_EventHandle'$1_voting_ResolveProposal'(x, $guid#$1_event_EventHandle'$1_voting_ResolveProposal'(s))
}
function {:inline} $Update'$1_event_EventHandle'$1_voting_ResolveProposal''_guid(s: $1_event_EventHandle'$1_voting_ResolveProposal', x: $1_guid_GUID): $1_event_EventHandle'$1_voting_ResolveProposal' {
    $1_event_EventHandle'$1_voting_ResolveProposal'($counter#$1_event_EventHandle'$1_voting_ResolveProposal'(s), x)
}
function $IsValid'$1_event_EventHandle'$1_voting_ResolveProposal''(s: $1_event_EventHandle'$1_voting_ResolveProposal'): bool {
    $IsValid'u64'($counter#$1_event_EventHandle'$1_voting_ResolveProposal'(s))
      && $IsValid'$1_guid_GUID'($guid#$1_event_EventHandle'$1_voting_ResolveProposal'(s))
}
function {:inline} $IsEqual'$1_event_EventHandle'$1_voting_ResolveProposal''(s1: $1_event_EventHandle'$1_voting_ResolveProposal', s2: $1_event_EventHandle'$1_voting_ResolveProposal'): bool {
    s1 == s2
}

// struct event::EventHandle<voting::VoteEvent> at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/event.move:16:5+224
type {:datatype} $1_event_EventHandle'$1_voting_VoteEvent';
function {:constructor} $1_event_EventHandle'$1_voting_VoteEvent'($counter: int, $guid: $1_guid_GUID): $1_event_EventHandle'$1_voting_VoteEvent';
function {:inline} $Update'$1_event_EventHandle'$1_voting_VoteEvent''_counter(s: $1_event_EventHandle'$1_voting_VoteEvent', x: int): $1_event_EventHandle'$1_voting_VoteEvent' {
    $1_event_EventHandle'$1_voting_VoteEvent'(x, $guid#$1_event_EventHandle'$1_voting_VoteEvent'(s))
}
function {:inline} $Update'$1_event_EventHandle'$1_voting_VoteEvent''_guid(s: $1_event_EventHandle'$1_voting_VoteEvent', x: $1_guid_GUID): $1_event_EventHandle'$1_voting_VoteEvent' {
    $1_event_EventHandle'$1_voting_VoteEvent'($counter#$1_event_EventHandle'$1_voting_VoteEvent'(s), x)
}
function $IsValid'$1_event_EventHandle'$1_voting_VoteEvent''(s: $1_event_EventHandle'$1_voting_VoteEvent'): bool {
    $IsValid'u64'($counter#$1_event_EventHandle'$1_voting_VoteEvent'(s))
      && $IsValid'$1_guid_GUID'($guid#$1_event_EventHandle'$1_voting_VoteEvent'(s))
}
function {:inline} $IsEqual'$1_event_EventHandle'$1_voting_VoteEvent''(s1: $1_event_EventHandle'$1_voting_VoteEvent', s2: $1_event_EventHandle'$1_voting_VoteEvent'): bool {
    s1 == s2
}

// struct event::EventHandle<reconfiguration::NewEpochEvent> at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/event.move:16:5+224
type {:datatype} $1_event_EventHandle'$1_reconfiguration_NewEpochEvent';
function {:constructor} $1_event_EventHandle'$1_reconfiguration_NewEpochEvent'($counter: int, $guid: $1_guid_GUID): $1_event_EventHandle'$1_reconfiguration_NewEpochEvent';
function {:inline} $Update'$1_event_EventHandle'$1_reconfiguration_NewEpochEvent''_counter(s: $1_event_EventHandle'$1_reconfiguration_NewEpochEvent', x: int): $1_event_EventHandle'$1_reconfiguration_NewEpochEvent' {
    $1_event_EventHandle'$1_reconfiguration_NewEpochEvent'(x, $guid#$1_event_EventHandle'$1_reconfiguration_NewEpochEvent'(s))
}
function {:inline} $Update'$1_event_EventHandle'$1_reconfiguration_NewEpochEvent''_guid(s: $1_event_EventHandle'$1_reconfiguration_NewEpochEvent', x: $1_guid_GUID): $1_event_EventHandle'$1_reconfiguration_NewEpochEvent' {
    $1_event_EventHandle'$1_reconfiguration_NewEpochEvent'($counter#$1_event_EventHandle'$1_reconfiguration_NewEpochEvent'(s), x)
}
function $IsValid'$1_event_EventHandle'$1_reconfiguration_NewEpochEvent''(s: $1_event_EventHandle'$1_reconfiguration_NewEpochEvent'): bool {
    $IsValid'u64'($counter#$1_event_EventHandle'$1_reconfiguration_NewEpochEvent'(s))
      && $IsValid'$1_guid_GUID'($guid#$1_event_EventHandle'$1_reconfiguration_NewEpochEvent'(s))
}
function {:inline} $IsEqual'$1_event_EventHandle'$1_reconfiguration_NewEpochEvent''(s1: $1_event_EventHandle'$1_reconfiguration_NewEpochEvent', s2: $1_event_EventHandle'$1_reconfiguration_NewEpochEvent'): bool {
    s1 == s2
}

// struct event::EventHandle<block::NewBlockEvent> at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/event.move:16:5+224
type {:datatype} $1_event_EventHandle'$1_block_NewBlockEvent';
function {:constructor} $1_event_EventHandle'$1_block_NewBlockEvent'($counter: int, $guid: $1_guid_GUID): $1_event_EventHandle'$1_block_NewBlockEvent';
function {:inline} $Update'$1_event_EventHandle'$1_block_NewBlockEvent''_counter(s: $1_event_EventHandle'$1_block_NewBlockEvent', x: int): $1_event_EventHandle'$1_block_NewBlockEvent' {
    $1_event_EventHandle'$1_block_NewBlockEvent'(x, $guid#$1_event_EventHandle'$1_block_NewBlockEvent'(s))
}
function {:inline} $Update'$1_event_EventHandle'$1_block_NewBlockEvent''_guid(s: $1_event_EventHandle'$1_block_NewBlockEvent', x: $1_guid_GUID): $1_event_EventHandle'$1_block_NewBlockEvent' {
    $1_event_EventHandle'$1_block_NewBlockEvent'($counter#$1_event_EventHandle'$1_block_NewBlockEvent'(s), x)
}
function $IsValid'$1_event_EventHandle'$1_block_NewBlockEvent''(s: $1_event_EventHandle'$1_block_NewBlockEvent'): bool {
    $IsValid'u64'($counter#$1_event_EventHandle'$1_block_NewBlockEvent'(s))
      && $IsValid'$1_guid_GUID'($guid#$1_event_EventHandle'$1_block_NewBlockEvent'(s))
}
function {:inline} $IsEqual'$1_event_EventHandle'$1_block_NewBlockEvent''(s1: $1_event_EventHandle'$1_block_NewBlockEvent', s2: $1_event_EventHandle'$1_block_NewBlockEvent'): bool {
    s1 == s2
}

// struct event::EventHandle<block::UpdateEpochIntervalEvent> at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/event.move:16:5+224
type {:datatype} $1_event_EventHandle'$1_block_UpdateEpochIntervalEvent';
function {:constructor} $1_event_EventHandle'$1_block_UpdateEpochIntervalEvent'($counter: int, $guid: $1_guid_GUID): $1_event_EventHandle'$1_block_UpdateEpochIntervalEvent';
function {:inline} $Update'$1_event_EventHandle'$1_block_UpdateEpochIntervalEvent''_counter(s: $1_event_EventHandle'$1_block_UpdateEpochIntervalEvent', x: int): $1_event_EventHandle'$1_block_UpdateEpochIntervalEvent' {
    $1_event_EventHandle'$1_block_UpdateEpochIntervalEvent'(x, $guid#$1_event_EventHandle'$1_block_UpdateEpochIntervalEvent'(s))
}
function {:inline} $Update'$1_event_EventHandle'$1_block_UpdateEpochIntervalEvent''_guid(s: $1_event_EventHandle'$1_block_UpdateEpochIntervalEvent', x: $1_guid_GUID): $1_event_EventHandle'$1_block_UpdateEpochIntervalEvent' {
    $1_event_EventHandle'$1_block_UpdateEpochIntervalEvent'($counter#$1_event_EventHandle'$1_block_UpdateEpochIntervalEvent'(s), x)
}
function $IsValid'$1_event_EventHandle'$1_block_UpdateEpochIntervalEvent''(s: $1_event_EventHandle'$1_block_UpdateEpochIntervalEvent'): bool {
    $IsValid'u64'($counter#$1_event_EventHandle'$1_block_UpdateEpochIntervalEvent'(s))
      && $IsValid'$1_guid_GUID'($guid#$1_event_EventHandle'$1_block_UpdateEpochIntervalEvent'(s))
}
function {:inline} $IsEqual'$1_event_EventHandle'$1_block_UpdateEpochIntervalEvent''(s1: $1_event_EventHandle'$1_block_UpdateEpochIntervalEvent', s2: $1_event_EventHandle'$1_block_UpdateEpochIntervalEvent'): bool {
    s1 == s2
}

// struct account::SignerCapability at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/account.move:49:5+60
type {:datatype} $1_account_SignerCapability;
function {:constructor} $1_account_SignerCapability($account: int): $1_account_SignerCapability;
function {:inline} $Update'$1_account_SignerCapability'_account(s: $1_account_SignerCapability, x: int): $1_account_SignerCapability {
    $1_account_SignerCapability(x)
}
function $IsValid'$1_account_SignerCapability'(s: $1_account_SignerCapability): bool {
    $IsValid'address'($account#$1_account_SignerCapability(s))
}
function {:inline} $IsEqual'$1_account_SignerCapability'(s1: $1_account_SignerCapability, s2: $1_account_SignerCapability): bool {
    s1 == s2
}

// fun account::create_signer_with_capability [baseline] at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/account.move:707:5+156
procedure {:inline 1} $1_account_create_signer_with_capability(_$t0: $1_account_SignerCapability) returns ($ret0: $signer)
{
    // declare local variables
    var $t1: int;
    var $t2: int;
    var $t3: $signer;
    var $t0: $1_account_SignerCapability;
    var $temp_0'$1_account_SignerCapability': $1_account_SignerCapability;
    var $temp_0'signer': $signer;
    $t0 := _$t0;

    // bytecode translation starts here
    // assume Identical($t1, select account::SignerCapability.account($t0)) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/account.spec.move:458:9+30
    assume {:print "$at(73,22246,22276)"} true;
    assume ($t1 == $account#$1_account_SignerCapability($t0));

    // trace_local[capability]($t0) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/account.move:707:5+1
    assume {:print "$at(72,39859,39860)"} true;
    assume {:print "$track_local(18,8,0):", $t0} $t0 == $t0;

    // $t2 := get_field<account::SignerCapability>.account($t0) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/account.move:708:20+19
    assume {:print "$at(72,39960,39979)"} true;
    $t2 := $account#$1_account_SignerCapability($t0);

    // $t3 := opaque begin: create_signer::create_signer($t2) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/account.move:709:9+20
    assume {:print "$at(72,39989,40009)"} true;

    // assume WellFormed($t3) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/account.move:709:9+20
    assume $IsValid'signer'($t3) && $1_signer_is_txn_signer($t3) && $1_signer_is_txn_signer_addr($addr#$signer($t3));

    // assume Eq<address>(signer::$address_of($t3), $t2) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/account.move:709:9+20
    assume $IsEqual'address'($1_signer_$address_of($t3), $t2);

    // $t3 := opaque end: create_signer::create_signer($t2) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/account.move:709:9+20

    // trace_return[0]($t3) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/account.move:709:9+20
    assume {:print "$track_return(18,8,0):", $t3} $t3 == $t3;

    // label L1 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/account.move:710:5+1
    assume {:print "$at(72,40014,40015)"} true;
L1:

    // return $t3 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/account.move:710:5+1
    assume {:print "$at(72,40014,40015)"} true;
    $ret0 := $t3;
    return;

}

// struct coin::BurnCapability<aptos_coin::AptosCoin> at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.move:139:5+58
type {:datatype} $1_coin_BurnCapability'$1_aptos_coin_AptosCoin';
function {:constructor} $1_coin_BurnCapability'$1_aptos_coin_AptosCoin'($dummy_field: bool): $1_coin_BurnCapability'$1_aptos_coin_AptosCoin';
function {:inline} $Update'$1_coin_BurnCapability'$1_aptos_coin_AptosCoin''_dummy_field(s: $1_coin_BurnCapability'$1_aptos_coin_AptosCoin', x: bool): $1_coin_BurnCapability'$1_aptos_coin_AptosCoin' {
    $1_coin_BurnCapability'$1_aptos_coin_AptosCoin'(x)
}
function $IsValid'$1_coin_BurnCapability'$1_aptos_coin_AptosCoin''(s: $1_coin_BurnCapability'$1_aptos_coin_AptosCoin'): bool {
    $IsValid'bool'($dummy_field#$1_coin_BurnCapability'$1_aptos_coin_AptosCoin'(s))
}
function {:inline} $IsEqual'$1_coin_BurnCapability'$1_aptos_coin_AptosCoin''(s1: $1_coin_BurnCapability'$1_aptos_coin_AptosCoin', s2: $1_coin_BurnCapability'$1_aptos_coin_AptosCoin'): bool {
    s1 == s2
}

// struct coin::MintCapability<aptos_coin::AptosCoin> at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.move:133:5+58
type {:datatype} $1_coin_MintCapability'$1_aptos_coin_AptosCoin';
function {:constructor} $1_coin_MintCapability'$1_aptos_coin_AptosCoin'($dummy_field: bool): $1_coin_MintCapability'$1_aptos_coin_AptosCoin';
function {:inline} $Update'$1_coin_MintCapability'$1_aptos_coin_AptosCoin''_dummy_field(s: $1_coin_MintCapability'$1_aptos_coin_AptosCoin', x: bool): $1_coin_MintCapability'$1_aptos_coin_AptosCoin' {
    $1_coin_MintCapability'$1_aptos_coin_AptosCoin'(x)
}
function $IsValid'$1_coin_MintCapability'$1_aptos_coin_AptosCoin''(s: $1_coin_MintCapability'$1_aptos_coin_AptosCoin'): bool {
    $IsValid'bool'($dummy_field#$1_coin_MintCapability'$1_aptos_coin_AptosCoin'(s))
}
function {:inline} $IsEqual'$1_coin_MintCapability'$1_aptos_coin_AptosCoin''(s1: $1_coin_MintCapability'$1_aptos_coin_AptosCoin', s2: $1_coin_MintCapability'$1_aptos_coin_AptosCoin'): bool {
    s1 == s2
}

// struct aptos_coin::AptosCoin at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:22:5+27
type {:datatype} $1_aptos_coin_AptosCoin;
function {:constructor} $1_aptos_coin_AptosCoin($dummy_field: bool): $1_aptos_coin_AptosCoin;
function {:inline} $Update'$1_aptos_coin_AptosCoin'_dummy_field(s: $1_aptos_coin_AptosCoin, x: bool): $1_aptos_coin_AptosCoin {
    $1_aptos_coin_AptosCoin(x)
}
function $IsValid'$1_aptos_coin_AptosCoin'(s: $1_aptos_coin_AptosCoin): bool {
    $IsValid'bool'($dummy_field#$1_aptos_coin_AptosCoin(s))
}
function {:inline} $IsEqual'$1_aptos_coin_AptosCoin'(s1: $1_aptos_coin_AptosCoin, s2: $1_aptos_coin_AptosCoin): bool {
    s1 == s2
}
var $1_aptos_coin_AptosCoin_$memory: $Memory $1_aptos_coin_AptosCoin;

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/transaction_context.spec.move:8:10+39
function  $1_transaction_context_spec_get_script_hash(): Vec (int);
axiom (var $$res := $1_transaction_context_spec_get_script_hash();
$IsValid'vec'u8''($$res));

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/chain_status.move:35:5+90
function {:inline} $1_chain_status_$is_operating($1_chain_status_GenesisEndMarker_$memory: $Memory $1_chain_status_GenesisEndMarker): bool {
    $ResourceExists($1_chain_status_GenesisEndMarker_$memory, 1)
}

// struct chain_status::GenesisEndMarker at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/chain_status.move:12:5+34
type {:datatype} $1_chain_status_GenesisEndMarker;
function {:constructor} $1_chain_status_GenesisEndMarker($dummy_field: bool): $1_chain_status_GenesisEndMarker;
function {:inline} $Update'$1_chain_status_GenesisEndMarker'_dummy_field(s: $1_chain_status_GenesisEndMarker, x: bool): $1_chain_status_GenesisEndMarker {
    $1_chain_status_GenesisEndMarker(x)
}
function $IsValid'$1_chain_status_GenesisEndMarker'(s: $1_chain_status_GenesisEndMarker): bool {
    $IsValid'bool'($dummy_field#$1_chain_status_GenesisEndMarker(s))
}
function {:inline} $IsEqual'$1_chain_status_GenesisEndMarker'(s1: $1_chain_status_GenesisEndMarker, s2: $1_chain_status_GenesisEndMarker): bool {
    s1 == s2
}
var $1_chain_status_GenesisEndMarker_$memory: $Memory $1_chain_status_GenesisEndMarker;

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/timestamp.move:61:5+153
function {:inline} $1_timestamp_$now_microseconds($1_timestamp_CurrentTimeMicroseconds_$memory: $Memory $1_timestamp_CurrentTimeMicroseconds): int {
    $microseconds#$1_timestamp_CurrentTimeMicroseconds($ResourceValue($1_timestamp_CurrentTimeMicroseconds_$memory, 1))
}

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/timestamp.move:67:5+123
function {:inline} $1_timestamp_$now_seconds($1_timestamp_CurrentTimeMicroseconds_$memory: $Memory $1_timestamp_CurrentTimeMicroseconds): int {
    ($1_timestamp_$now_microseconds($1_timestamp_CurrentTimeMicroseconds_$memory) div 1000000)
}

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/timestamp.spec.move:22:10+111
function {:inline} $1_timestamp_spec_now_microseconds($1_timestamp_CurrentTimeMicroseconds_$memory: $Memory $1_timestamp_CurrentTimeMicroseconds): int {
    $microseconds#$1_timestamp_CurrentTimeMicroseconds($ResourceValue($1_timestamp_CurrentTimeMicroseconds_$memory, 1))
}

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/timestamp.spec.move:26:10+93
function {:inline} $1_timestamp_spec_now_seconds($1_timestamp_CurrentTimeMicroseconds_$memory: $Memory $1_timestamp_CurrentTimeMicroseconds): int {
    ($1_timestamp_spec_now_microseconds($1_timestamp_CurrentTimeMicroseconds_$memory) div 1000000)
}

// struct timestamp::CurrentTimeMicroseconds at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/timestamp.move:12:5+73
type {:datatype} $1_timestamp_CurrentTimeMicroseconds;
function {:constructor} $1_timestamp_CurrentTimeMicroseconds($microseconds: int): $1_timestamp_CurrentTimeMicroseconds;
function {:inline} $Update'$1_timestamp_CurrentTimeMicroseconds'_microseconds(s: $1_timestamp_CurrentTimeMicroseconds, x: int): $1_timestamp_CurrentTimeMicroseconds {
    $1_timestamp_CurrentTimeMicroseconds(x)
}
function $IsValid'$1_timestamp_CurrentTimeMicroseconds'(s: $1_timestamp_CurrentTimeMicroseconds): bool {
    $IsValid'u64'($microseconds#$1_timestamp_CurrentTimeMicroseconds(s))
}
function {:inline} $IsEqual'$1_timestamp_CurrentTimeMicroseconds'(s1: $1_timestamp_CurrentTimeMicroseconds, s2: $1_timestamp_CurrentTimeMicroseconds): bool {
    s1 == s2
}
var $1_timestamp_CurrentTimeMicroseconds_$memory: $Memory $1_timestamp_CurrentTimeMicroseconds;

// fun timestamp::now_microseconds [baseline] at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/timestamp.move:61:5+153
procedure {:inline 1} $1_timestamp_now_microseconds() returns ($ret0: int)
{
    // declare local variables
    var $t0: int;
    var $t1: $1_timestamp_CurrentTimeMicroseconds;
    var $t2: int;
    var $t3: int;
    var $temp_0'u64': int;

    // bytecode translation starts here
    // $t0 := 0x1 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/timestamp.move:62:48+16
    assume {:print "$at(141,2511,2527)"} true;
    $t0 := 1;
    assume $IsValid'address'($t0);

    // $t1 := get_global<timestamp::CurrentTimeMicroseconds>($t0) on_abort goto L2 with $t2 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/timestamp.move:62:9+13
    if (!$ResourceExists($1_timestamp_CurrentTimeMicroseconds_$memory, $t0)) {
        call $ExecFailureAbort();
    } else {
        $t1 := $ResourceValue($1_timestamp_CurrentTimeMicroseconds_$memory, $t0);
    }
    if ($abort_flag) {
        assume {:print "$at(141,2472,2485)"} true;
        $t2 := $abort_code;
        assume {:print "$track_abort(28,0):", $t2} $t2 == $t2;
        goto L2;
    }

    // $t3 := get_field<timestamp::CurrentTimeMicroseconds>.microseconds($t1) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/timestamp.move:62:9+69
    $t3 := $microseconds#$1_timestamp_CurrentTimeMicroseconds($t1);

    // trace_return[0]($t3) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/timestamp.move:62:9+69
    assume {:print "$track_return(28,0,0):", $t3} $t3 == $t3;

    // label L1 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/timestamp.move:63:5+1
    assume {:print "$at(141,2546,2547)"} true;
L1:

    // return $t3 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/timestamp.move:63:5+1
    assume {:print "$at(141,2546,2547)"} true;
    $ret0 := $t3;
    return;

    // label L2 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/timestamp.move:63:5+1
L2:

    // abort($t2) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/timestamp.move:63:5+1
    assume {:print "$at(141,2546,2547)"} true;
    $abort_code := $t2;
    $abort_flag := true;
    return;

}

// fun timestamp::now_seconds [baseline] at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/timestamp.move:67:5+123
procedure {:inline 1} $1_timestamp_now_seconds() returns ($ret0: int)
{
    // declare local variables
    var $t0: int;
    var $t1: int;
    var $t2: int;
    var $t3: int;
    var $temp_0'u64': int;

    // bytecode translation starts here
    // $t0 := timestamp::now_microseconds() on_abort goto L2 with $t1 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/timestamp.move:68:9+18
    assume {:print "$at(141,2680,2698)"} true;
    call $t0 := $1_timestamp_now_microseconds();
    if ($abort_flag) {
        assume {:print "$at(141,2680,2698)"} true;
        $t1 := $abort_code;
        assume {:print "$track_abort(28,1):", $t1} $t1 == $t1;
        goto L2;
    }

    // $t2 := 1000000 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/timestamp.move:68:30+23
    $t2 := 1000000;
    assume $IsValid'u64'($t2);

    // $t3 := /($t0, $t2) on_abort goto L2 with $t1 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/timestamp.move:68:28+1
    call $t3 := $Div($t0, $t2);
    if ($abort_flag) {
        assume {:print "$at(141,2699,2700)"} true;
        $t1 := $abort_code;
        assume {:print "$track_abort(28,1):", $t1} $t1 == $t1;
        goto L2;
    }

    // trace_return[0]($t3) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/timestamp.move:68:9+44
    assume {:print "$track_return(28,1,0):", $t3} $t3 == $t3;

    // label L1 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/timestamp.move:69:5+1
    assume {:print "$at(141,2729,2730)"} true;
L1:

    // return $t3 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/timestamp.move:69:5+1
    assume {:print "$at(141,2729,2730)"} true;
    $ret0 := $t3;
    return;

    // label L2 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/timestamp.move:69:5+1
L2:

    // abort($t1) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/timestamp.move:69:5+1
    assume {:print "$at(141,2729,2730)"} true;
    $abort_code := $t1;
    $abort_flag := true;
    return;

}

// struct voting::CreateProposalEvent at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:142:5+280
type {:datatype} $1_voting_CreateProposalEvent;
function {:constructor} $1_voting_CreateProposalEvent($proposal_id: int, $early_resolution_vote_threshold: $1_option_Option'u128', $execution_hash: Vec (int), $expiration_secs: int, $metadata: Table int (Vec (int)), $min_vote_threshold: int): $1_voting_CreateProposalEvent;
function {:inline} $Update'$1_voting_CreateProposalEvent'_proposal_id(s: $1_voting_CreateProposalEvent, x: int): $1_voting_CreateProposalEvent {
    $1_voting_CreateProposalEvent(x, $early_resolution_vote_threshold#$1_voting_CreateProposalEvent(s), $execution_hash#$1_voting_CreateProposalEvent(s), $expiration_secs#$1_voting_CreateProposalEvent(s), $metadata#$1_voting_CreateProposalEvent(s), $min_vote_threshold#$1_voting_CreateProposalEvent(s))
}
function {:inline} $Update'$1_voting_CreateProposalEvent'_early_resolution_vote_threshold(s: $1_voting_CreateProposalEvent, x: $1_option_Option'u128'): $1_voting_CreateProposalEvent {
    $1_voting_CreateProposalEvent($proposal_id#$1_voting_CreateProposalEvent(s), x, $execution_hash#$1_voting_CreateProposalEvent(s), $expiration_secs#$1_voting_CreateProposalEvent(s), $metadata#$1_voting_CreateProposalEvent(s), $min_vote_threshold#$1_voting_CreateProposalEvent(s))
}
function {:inline} $Update'$1_voting_CreateProposalEvent'_execution_hash(s: $1_voting_CreateProposalEvent, x: Vec (int)): $1_voting_CreateProposalEvent {
    $1_voting_CreateProposalEvent($proposal_id#$1_voting_CreateProposalEvent(s), $early_resolution_vote_threshold#$1_voting_CreateProposalEvent(s), x, $expiration_secs#$1_voting_CreateProposalEvent(s), $metadata#$1_voting_CreateProposalEvent(s), $min_vote_threshold#$1_voting_CreateProposalEvent(s))
}
function {:inline} $Update'$1_voting_CreateProposalEvent'_expiration_secs(s: $1_voting_CreateProposalEvent, x: int): $1_voting_CreateProposalEvent {
    $1_voting_CreateProposalEvent($proposal_id#$1_voting_CreateProposalEvent(s), $early_resolution_vote_threshold#$1_voting_CreateProposalEvent(s), $execution_hash#$1_voting_CreateProposalEvent(s), x, $metadata#$1_voting_CreateProposalEvent(s), $min_vote_threshold#$1_voting_CreateProposalEvent(s))
}
function {:inline} $Update'$1_voting_CreateProposalEvent'_metadata(s: $1_voting_CreateProposalEvent, x: Table int (Vec (int))): $1_voting_CreateProposalEvent {
    $1_voting_CreateProposalEvent($proposal_id#$1_voting_CreateProposalEvent(s), $early_resolution_vote_threshold#$1_voting_CreateProposalEvent(s), $execution_hash#$1_voting_CreateProposalEvent(s), $expiration_secs#$1_voting_CreateProposalEvent(s), x, $min_vote_threshold#$1_voting_CreateProposalEvent(s))
}
function {:inline} $Update'$1_voting_CreateProposalEvent'_min_vote_threshold(s: $1_voting_CreateProposalEvent, x: int): $1_voting_CreateProposalEvent {
    $1_voting_CreateProposalEvent($proposal_id#$1_voting_CreateProposalEvent(s), $early_resolution_vote_threshold#$1_voting_CreateProposalEvent(s), $execution_hash#$1_voting_CreateProposalEvent(s), $expiration_secs#$1_voting_CreateProposalEvent(s), $metadata#$1_voting_CreateProposalEvent(s), x)
}
function $IsValid'$1_voting_CreateProposalEvent'(s: $1_voting_CreateProposalEvent): bool {
    $IsValid'u64'($proposal_id#$1_voting_CreateProposalEvent(s))
      && $IsValid'$1_option_Option'u128''($early_resolution_vote_threshold#$1_voting_CreateProposalEvent(s))
      && $IsValid'vec'u8''($execution_hash#$1_voting_CreateProposalEvent(s))
      && $IsValid'u64'($expiration_secs#$1_voting_CreateProposalEvent(s))
      && $IsValid'$1_simple_map_SimpleMap'$1_string_String_vec'u8'''($metadata#$1_voting_CreateProposalEvent(s))
      && $IsValid'u128'($min_vote_threshold#$1_voting_CreateProposalEvent(s))
}
function {:inline} $IsEqual'$1_voting_CreateProposalEvent'(s1: $1_voting_CreateProposalEvent, s2: $1_voting_CreateProposalEvent): bool {
    $IsEqual'u64'($proposal_id#$1_voting_CreateProposalEvent(s1), $proposal_id#$1_voting_CreateProposalEvent(s2))
    && $IsEqual'$1_option_Option'u128''($early_resolution_vote_threshold#$1_voting_CreateProposalEvent(s1), $early_resolution_vote_threshold#$1_voting_CreateProposalEvent(s2))
    && $IsEqual'vec'u8''($execution_hash#$1_voting_CreateProposalEvent(s1), $execution_hash#$1_voting_CreateProposalEvent(s2))
    && $IsEqual'u64'($expiration_secs#$1_voting_CreateProposalEvent(s1), $expiration_secs#$1_voting_CreateProposalEvent(s2))
    && $IsEqual'$1_simple_map_SimpleMap'$1_string_String_vec'u8'''($metadata#$1_voting_CreateProposalEvent(s1), $metadata#$1_voting_CreateProposalEvent(s2))
    && $IsEqual'u128'($min_vote_threshold#$1_voting_CreateProposalEvent(s1), $min_vote_threshold#$1_voting_CreateProposalEvent(s2))}

// struct voting::Proposal<governance_proposal::GovernanceProposal> at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:81:5+2423
type {:datatype} $1_voting_Proposal'$1_governance_proposal_GovernanceProposal';
function {:constructor} $1_voting_Proposal'$1_governance_proposal_GovernanceProposal'($proposer: int, $execution_content: $1_option_Option'$1_governance_proposal_GovernanceProposal', $metadata: Table int (Vec (int)), $creation_time_secs: int, $execution_hash: Vec (int), $min_vote_threshold: int, $expiration_secs: int, $early_resolution_vote_threshold: $1_option_Option'u128', $yes_votes: int, $no_votes: int, $is_resolved: bool, $resolution_time_secs: int): $1_voting_Proposal'$1_governance_proposal_GovernanceProposal';
function {:inline} $Update'$1_voting_Proposal'$1_governance_proposal_GovernanceProposal''_proposer(s: $1_voting_Proposal'$1_governance_proposal_GovernanceProposal', x: int): $1_voting_Proposal'$1_governance_proposal_GovernanceProposal' {
    $1_voting_Proposal'$1_governance_proposal_GovernanceProposal'(x, $execution_content#$1_voting_Proposal'$1_governance_proposal_GovernanceProposal'(s), $metadata#$1_voting_Proposal'$1_governance_proposal_GovernanceProposal'(s), $creation_time_secs#$1_voting_Proposal'$1_governance_proposal_GovernanceProposal'(s), $execution_hash#$1_voting_Proposal'$1_governance_proposal_GovernanceProposal'(s), $min_vote_threshold#$1_voting_Proposal'$1_governance_proposal_GovernanceProposal'(s), $expiration_secs#$1_voting_Proposal'$1_governance_proposal_GovernanceProposal'(s), $early_resolution_vote_threshold#$1_voting_Proposal'$1_governance_proposal_GovernanceProposal'(s), $yes_votes#$1_voting_Proposal'$1_governance_proposal_GovernanceProposal'(s), $no_votes#$1_voting_Proposal'$1_governance_proposal_GovernanceProposal'(s), $is_resolved#$1_voting_Proposal'$1_governance_proposal_GovernanceProposal'(s), $resolution_time_secs#$1_voting_Proposal'$1_governance_proposal_GovernanceProposal'(s))
}
function {:inline} $Update'$1_voting_Proposal'$1_governance_proposal_GovernanceProposal''_execution_content(s: $1_voting_Proposal'$1_governance_proposal_GovernanceProposal', x: $1_option_Option'$1_governance_proposal_GovernanceProposal'): $1_voting_Proposal'$1_governance_proposal_GovernanceProposal' {
    $1_voting_Proposal'$1_governance_proposal_GovernanceProposal'($proposer#$1_voting_Proposal'$1_governance_proposal_GovernanceProposal'(s), x, $metadata#$1_voting_Proposal'$1_governance_proposal_GovernanceProposal'(s), $creation_time_secs#$1_voting_Proposal'$1_governance_proposal_GovernanceProposal'(s), $execution_hash#$1_voting_Proposal'$1_governance_proposal_GovernanceProposal'(s), $min_vote_threshold#$1_voting_Proposal'$1_governance_proposal_GovernanceProposal'(s), $expiration_secs#$1_voting_Proposal'$1_governance_proposal_GovernanceProposal'(s), $early_resolution_vote_threshold#$1_voting_Proposal'$1_governance_proposal_GovernanceProposal'(s), $yes_votes#$1_voting_Proposal'$1_governance_proposal_GovernanceProposal'(s), $no_votes#$1_voting_Proposal'$1_governance_proposal_GovernanceProposal'(s), $is_resolved#$1_voting_Proposal'$1_governance_proposal_GovernanceProposal'(s), $resolution_time_secs#$1_voting_Proposal'$1_governance_proposal_GovernanceProposal'(s))
}
function {:inline} $Update'$1_voting_Proposal'$1_governance_proposal_GovernanceProposal''_metadata(s: $1_voting_Proposal'$1_governance_proposal_GovernanceProposal', x: Table int (Vec (int))): $1_voting_Proposal'$1_governance_proposal_GovernanceProposal' {
    $1_voting_Proposal'$1_governance_proposal_GovernanceProposal'($proposer#$1_voting_Proposal'$1_governance_proposal_GovernanceProposal'(s), $execution_content#$1_voting_Proposal'$1_governance_proposal_GovernanceProposal'(s), x, $creation_time_secs#$1_voting_Proposal'$1_governance_proposal_GovernanceProposal'(s), $execution_hash#$1_voting_Proposal'$1_governance_proposal_GovernanceProposal'(s), $min_vote_threshold#$1_voting_Proposal'$1_governance_proposal_GovernanceProposal'(s), $expiration_secs#$1_voting_Proposal'$1_governance_proposal_GovernanceProposal'(s), $early_resolution_vote_threshold#$1_voting_Proposal'$1_governance_proposal_GovernanceProposal'(s), $yes_votes#$1_voting_Proposal'$1_governance_proposal_GovernanceProposal'(s), $no_votes#$1_voting_Proposal'$1_governance_proposal_GovernanceProposal'(s), $is_resolved#$1_voting_Proposal'$1_governance_proposal_GovernanceProposal'(s), $resolution_time_secs#$1_voting_Proposal'$1_governance_proposal_GovernanceProposal'(s))
}
function {:inline} $Update'$1_voting_Proposal'$1_governance_proposal_GovernanceProposal''_creation_time_secs(s: $1_voting_Proposal'$1_governance_proposal_GovernanceProposal', x: int): $1_voting_Proposal'$1_governance_proposal_GovernanceProposal' {
    $1_voting_Proposal'$1_governance_proposal_GovernanceProposal'($proposer#$1_voting_Proposal'$1_governance_proposal_GovernanceProposal'(s), $execution_content#$1_voting_Proposal'$1_governance_proposal_GovernanceProposal'(s), $metadata#$1_voting_Proposal'$1_governance_proposal_GovernanceProposal'(s), x, $execution_hash#$1_voting_Proposal'$1_governance_proposal_GovernanceProposal'(s), $min_vote_threshold#$1_voting_Proposal'$1_governance_proposal_GovernanceProposal'(s), $expiration_secs#$1_voting_Proposal'$1_governance_proposal_GovernanceProposal'(s), $early_resolution_vote_threshold#$1_voting_Proposal'$1_governance_proposal_GovernanceProposal'(s), $yes_votes#$1_voting_Proposal'$1_governance_proposal_GovernanceProposal'(s), $no_votes#$1_voting_Proposal'$1_governance_proposal_GovernanceProposal'(s), $is_resolved#$1_voting_Proposal'$1_governance_proposal_GovernanceProposal'(s), $resolution_time_secs#$1_voting_Proposal'$1_governance_proposal_GovernanceProposal'(s))
}
function {:inline} $Update'$1_voting_Proposal'$1_governance_proposal_GovernanceProposal''_execution_hash(s: $1_voting_Proposal'$1_governance_proposal_GovernanceProposal', x: Vec (int)): $1_voting_Proposal'$1_governance_proposal_GovernanceProposal' {
    $1_voting_Proposal'$1_governance_proposal_GovernanceProposal'($proposer#$1_voting_Proposal'$1_governance_proposal_GovernanceProposal'(s), $execution_content#$1_voting_Proposal'$1_governance_proposal_GovernanceProposal'(s), $metadata#$1_voting_Proposal'$1_governance_proposal_GovernanceProposal'(s), $creation_time_secs#$1_voting_Proposal'$1_governance_proposal_GovernanceProposal'(s), x, $min_vote_threshold#$1_voting_Proposal'$1_governance_proposal_GovernanceProposal'(s), $expiration_secs#$1_voting_Proposal'$1_governance_proposal_GovernanceProposal'(s), $early_resolution_vote_threshold#$1_voting_Proposal'$1_governance_proposal_GovernanceProposal'(s), $yes_votes#$1_voting_Proposal'$1_governance_proposal_GovernanceProposal'(s), $no_votes#$1_voting_Proposal'$1_governance_proposal_GovernanceProposal'(s), $is_resolved#$1_voting_Proposal'$1_governance_proposal_GovernanceProposal'(s), $resolution_time_secs#$1_voting_Proposal'$1_governance_proposal_GovernanceProposal'(s))
}
function {:inline} $Update'$1_voting_Proposal'$1_governance_proposal_GovernanceProposal''_min_vote_threshold(s: $1_voting_Proposal'$1_governance_proposal_GovernanceProposal', x: int): $1_voting_Proposal'$1_governance_proposal_GovernanceProposal' {
    $1_voting_Proposal'$1_governance_proposal_GovernanceProposal'($proposer#$1_voting_Proposal'$1_governance_proposal_GovernanceProposal'(s), $execution_content#$1_voting_Proposal'$1_governance_proposal_GovernanceProposal'(s), $metadata#$1_voting_Proposal'$1_governance_proposal_GovernanceProposal'(s), $creation_time_secs#$1_voting_Proposal'$1_governance_proposal_GovernanceProposal'(s), $execution_hash#$1_voting_Proposal'$1_governance_proposal_GovernanceProposal'(s), x, $expiration_secs#$1_voting_Proposal'$1_governance_proposal_GovernanceProposal'(s), $early_resolution_vote_threshold#$1_voting_Proposal'$1_governance_proposal_GovernanceProposal'(s), $yes_votes#$1_voting_Proposal'$1_governance_proposal_GovernanceProposal'(s), $no_votes#$1_voting_Proposal'$1_governance_proposal_GovernanceProposal'(s), $is_resolved#$1_voting_Proposal'$1_governance_proposal_GovernanceProposal'(s), $resolution_time_secs#$1_voting_Proposal'$1_governance_proposal_GovernanceProposal'(s))
}
function {:inline} $Update'$1_voting_Proposal'$1_governance_proposal_GovernanceProposal''_expiration_secs(s: $1_voting_Proposal'$1_governance_proposal_GovernanceProposal', x: int): $1_voting_Proposal'$1_governance_proposal_GovernanceProposal' {
    $1_voting_Proposal'$1_governance_proposal_GovernanceProposal'($proposer#$1_voting_Proposal'$1_governance_proposal_GovernanceProposal'(s), $execution_content#$1_voting_Proposal'$1_governance_proposal_GovernanceProposal'(s), $metadata#$1_voting_Proposal'$1_governance_proposal_GovernanceProposal'(s), $creation_time_secs#$1_voting_Proposal'$1_governance_proposal_GovernanceProposal'(s), $execution_hash#$1_voting_Proposal'$1_governance_proposal_GovernanceProposal'(s), $min_vote_threshold#$1_voting_Proposal'$1_governance_proposal_GovernanceProposal'(s), x, $early_resolution_vote_threshold#$1_voting_Proposal'$1_governance_proposal_GovernanceProposal'(s), $yes_votes#$1_voting_Proposal'$1_governance_proposal_GovernanceProposal'(s), $no_votes#$1_voting_Proposal'$1_governance_proposal_GovernanceProposal'(s), $is_resolved#$1_voting_Proposal'$1_governance_proposal_GovernanceProposal'(s), $resolution_time_secs#$1_voting_Proposal'$1_governance_proposal_GovernanceProposal'(s))
}
function {:inline} $Update'$1_voting_Proposal'$1_governance_proposal_GovernanceProposal''_early_resolution_vote_threshold(s: $1_voting_Proposal'$1_governance_proposal_GovernanceProposal', x: $1_option_Option'u128'): $1_voting_Proposal'$1_governance_proposal_GovernanceProposal' {
    $1_voting_Proposal'$1_governance_proposal_GovernanceProposal'($proposer#$1_voting_Proposal'$1_governance_proposal_GovernanceProposal'(s), $execution_content#$1_voting_Proposal'$1_governance_proposal_GovernanceProposal'(s), $metadata#$1_voting_Proposal'$1_governance_proposal_GovernanceProposal'(s), $creation_time_secs#$1_voting_Proposal'$1_governance_proposal_GovernanceProposal'(s), $execution_hash#$1_voting_Proposal'$1_governance_proposal_GovernanceProposal'(s), $min_vote_threshold#$1_voting_Proposal'$1_governance_proposal_GovernanceProposal'(s), $expiration_secs#$1_voting_Proposal'$1_governance_proposal_GovernanceProposal'(s), x, $yes_votes#$1_voting_Proposal'$1_governance_proposal_GovernanceProposal'(s), $no_votes#$1_voting_Proposal'$1_governance_proposal_GovernanceProposal'(s), $is_resolved#$1_voting_Proposal'$1_governance_proposal_GovernanceProposal'(s), $resolution_time_secs#$1_voting_Proposal'$1_governance_proposal_GovernanceProposal'(s))
}
function {:inline} $Update'$1_voting_Proposal'$1_governance_proposal_GovernanceProposal''_yes_votes(s: $1_voting_Proposal'$1_governance_proposal_GovernanceProposal', x: int): $1_voting_Proposal'$1_governance_proposal_GovernanceProposal' {
    $1_voting_Proposal'$1_governance_proposal_GovernanceProposal'($proposer#$1_voting_Proposal'$1_governance_proposal_GovernanceProposal'(s), $execution_content#$1_voting_Proposal'$1_governance_proposal_GovernanceProposal'(s), $metadata#$1_voting_Proposal'$1_governance_proposal_GovernanceProposal'(s), $creation_time_secs#$1_voting_Proposal'$1_governance_proposal_GovernanceProposal'(s), $execution_hash#$1_voting_Proposal'$1_governance_proposal_GovernanceProposal'(s), $min_vote_threshold#$1_voting_Proposal'$1_governance_proposal_GovernanceProposal'(s), $expiration_secs#$1_voting_Proposal'$1_governance_proposal_GovernanceProposal'(s), $early_resolution_vote_threshold#$1_voting_Proposal'$1_governance_proposal_GovernanceProposal'(s), x, $no_votes#$1_voting_Proposal'$1_governance_proposal_GovernanceProposal'(s), $is_resolved#$1_voting_Proposal'$1_governance_proposal_GovernanceProposal'(s), $resolution_time_secs#$1_voting_Proposal'$1_governance_proposal_GovernanceProposal'(s))
}
function {:inline} $Update'$1_voting_Proposal'$1_governance_proposal_GovernanceProposal''_no_votes(s: $1_voting_Proposal'$1_governance_proposal_GovernanceProposal', x: int): $1_voting_Proposal'$1_governance_proposal_GovernanceProposal' {
    $1_voting_Proposal'$1_governance_proposal_GovernanceProposal'($proposer#$1_voting_Proposal'$1_governance_proposal_GovernanceProposal'(s), $execution_content#$1_voting_Proposal'$1_governance_proposal_GovernanceProposal'(s), $metadata#$1_voting_Proposal'$1_governance_proposal_GovernanceProposal'(s), $creation_time_secs#$1_voting_Proposal'$1_governance_proposal_GovernanceProposal'(s), $execution_hash#$1_voting_Proposal'$1_governance_proposal_GovernanceProposal'(s), $min_vote_threshold#$1_voting_Proposal'$1_governance_proposal_GovernanceProposal'(s), $expiration_secs#$1_voting_Proposal'$1_governance_proposal_GovernanceProposal'(s), $early_resolution_vote_threshold#$1_voting_Proposal'$1_governance_proposal_GovernanceProposal'(s), $yes_votes#$1_voting_Proposal'$1_governance_proposal_GovernanceProposal'(s), x, $is_resolved#$1_voting_Proposal'$1_governance_proposal_GovernanceProposal'(s), $resolution_time_secs#$1_voting_Proposal'$1_governance_proposal_GovernanceProposal'(s))
}
function {:inline} $Update'$1_voting_Proposal'$1_governance_proposal_GovernanceProposal''_is_resolved(s: $1_voting_Proposal'$1_governance_proposal_GovernanceProposal', x: bool): $1_voting_Proposal'$1_governance_proposal_GovernanceProposal' {
    $1_voting_Proposal'$1_governance_proposal_GovernanceProposal'($proposer#$1_voting_Proposal'$1_governance_proposal_GovernanceProposal'(s), $execution_content#$1_voting_Proposal'$1_governance_proposal_GovernanceProposal'(s), $metadata#$1_voting_Proposal'$1_governance_proposal_GovernanceProposal'(s), $creation_time_secs#$1_voting_Proposal'$1_governance_proposal_GovernanceProposal'(s), $execution_hash#$1_voting_Proposal'$1_governance_proposal_GovernanceProposal'(s), $min_vote_threshold#$1_voting_Proposal'$1_governance_proposal_GovernanceProposal'(s), $expiration_secs#$1_voting_Proposal'$1_governance_proposal_GovernanceProposal'(s), $early_resolution_vote_threshold#$1_voting_Proposal'$1_governance_proposal_GovernanceProposal'(s), $yes_votes#$1_voting_Proposal'$1_governance_proposal_GovernanceProposal'(s), $no_votes#$1_voting_Proposal'$1_governance_proposal_GovernanceProposal'(s), x, $resolution_time_secs#$1_voting_Proposal'$1_governance_proposal_GovernanceProposal'(s))
}
function {:inline} $Update'$1_voting_Proposal'$1_governance_proposal_GovernanceProposal''_resolution_time_secs(s: $1_voting_Proposal'$1_governance_proposal_GovernanceProposal', x: int): $1_voting_Proposal'$1_governance_proposal_GovernanceProposal' {
    $1_voting_Proposal'$1_governance_proposal_GovernanceProposal'($proposer#$1_voting_Proposal'$1_governance_proposal_GovernanceProposal'(s), $execution_content#$1_voting_Proposal'$1_governance_proposal_GovernanceProposal'(s), $metadata#$1_voting_Proposal'$1_governance_proposal_GovernanceProposal'(s), $creation_time_secs#$1_voting_Proposal'$1_governance_proposal_GovernanceProposal'(s), $execution_hash#$1_voting_Proposal'$1_governance_proposal_GovernanceProposal'(s), $min_vote_threshold#$1_voting_Proposal'$1_governance_proposal_GovernanceProposal'(s), $expiration_secs#$1_voting_Proposal'$1_governance_proposal_GovernanceProposal'(s), $early_resolution_vote_threshold#$1_voting_Proposal'$1_governance_proposal_GovernanceProposal'(s), $yes_votes#$1_voting_Proposal'$1_governance_proposal_GovernanceProposal'(s), $no_votes#$1_voting_Proposal'$1_governance_proposal_GovernanceProposal'(s), $is_resolved#$1_voting_Proposal'$1_governance_proposal_GovernanceProposal'(s), x)
}
function $IsValid'$1_voting_Proposal'$1_governance_proposal_GovernanceProposal''(s: $1_voting_Proposal'$1_governance_proposal_GovernanceProposal'): bool {
    $IsValid'address'($proposer#$1_voting_Proposal'$1_governance_proposal_GovernanceProposal'(s))
      && $IsValid'$1_option_Option'$1_governance_proposal_GovernanceProposal''($execution_content#$1_voting_Proposal'$1_governance_proposal_GovernanceProposal'(s))
      && $IsValid'$1_simple_map_SimpleMap'$1_string_String_vec'u8'''($metadata#$1_voting_Proposal'$1_governance_proposal_GovernanceProposal'(s))
      && $IsValid'u64'($creation_time_secs#$1_voting_Proposal'$1_governance_proposal_GovernanceProposal'(s))
      && $IsValid'vec'u8''($execution_hash#$1_voting_Proposal'$1_governance_proposal_GovernanceProposal'(s))
      && $IsValid'u128'($min_vote_threshold#$1_voting_Proposal'$1_governance_proposal_GovernanceProposal'(s))
      && $IsValid'u64'($expiration_secs#$1_voting_Proposal'$1_governance_proposal_GovernanceProposal'(s))
      && $IsValid'$1_option_Option'u128''($early_resolution_vote_threshold#$1_voting_Proposal'$1_governance_proposal_GovernanceProposal'(s))
      && $IsValid'u128'($yes_votes#$1_voting_Proposal'$1_governance_proposal_GovernanceProposal'(s))
      && $IsValid'u128'($no_votes#$1_voting_Proposal'$1_governance_proposal_GovernanceProposal'(s))
      && $IsValid'bool'($is_resolved#$1_voting_Proposal'$1_governance_proposal_GovernanceProposal'(s))
      && $IsValid'u64'($resolution_time_secs#$1_voting_Proposal'$1_governance_proposal_GovernanceProposal'(s))
}
function {:inline} $IsEqual'$1_voting_Proposal'$1_governance_proposal_GovernanceProposal''(s1: $1_voting_Proposal'$1_governance_proposal_GovernanceProposal', s2: $1_voting_Proposal'$1_governance_proposal_GovernanceProposal'): bool {
    $IsEqual'address'($proposer#$1_voting_Proposal'$1_governance_proposal_GovernanceProposal'(s1), $proposer#$1_voting_Proposal'$1_governance_proposal_GovernanceProposal'(s2))
    && $IsEqual'$1_option_Option'$1_governance_proposal_GovernanceProposal''($execution_content#$1_voting_Proposal'$1_governance_proposal_GovernanceProposal'(s1), $execution_content#$1_voting_Proposal'$1_governance_proposal_GovernanceProposal'(s2))
    && $IsEqual'$1_simple_map_SimpleMap'$1_string_String_vec'u8'''($metadata#$1_voting_Proposal'$1_governance_proposal_GovernanceProposal'(s1), $metadata#$1_voting_Proposal'$1_governance_proposal_GovernanceProposal'(s2))
    && $IsEqual'u64'($creation_time_secs#$1_voting_Proposal'$1_governance_proposal_GovernanceProposal'(s1), $creation_time_secs#$1_voting_Proposal'$1_governance_proposal_GovernanceProposal'(s2))
    && $IsEqual'vec'u8''($execution_hash#$1_voting_Proposal'$1_governance_proposal_GovernanceProposal'(s1), $execution_hash#$1_voting_Proposal'$1_governance_proposal_GovernanceProposal'(s2))
    && $IsEqual'u128'($min_vote_threshold#$1_voting_Proposal'$1_governance_proposal_GovernanceProposal'(s1), $min_vote_threshold#$1_voting_Proposal'$1_governance_proposal_GovernanceProposal'(s2))
    && $IsEqual'u64'($expiration_secs#$1_voting_Proposal'$1_governance_proposal_GovernanceProposal'(s1), $expiration_secs#$1_voting_Proposal'$1_governance_proposal_GovernanceProposal'(s2))
    && $IsEqual'$1_option_Option'u128''($early_resolution_vote_threshold#$1_voting_Proposal'$1_governance_proposal_GovernanceProposal'(s1), $early_resolution_vote_threshold#$1_voting_Proposal'$1_governance_proposal_GovernanceProposal'(s2))
    && $IsEqual'u128'($yes_votes#$1_voting_Proposal'$1_governance_proposal_GovernanceProposal'(s1), $yes_votes#$1_voting_Proposal'$1_governance_proposal_GovernanceProposal'(s2))
    && $IsEqual'u128'($no_votes#$1_voting_Proposal'$1_governance_proposal_GovernanceProposal'(s1), $no_votes#$1_voting_Proposal'$1_governance_proposal_GovernanceProposal'(s2))
    && $IsEqual'bool'($is_resolved#$1_voting_Proposal'$1_governance_proposal_GovernanceProposal'(s1), $is_resolved#$1_voting_Proposal'$1_governance_proposal_GovernanceProposal'(s2))
    && $IsEqual'u64'($resolution_time_secs#$1_voting_Proposal'$1_governance_proposal_GovernanceProposal'(s1), $resolution_time_secs#$1_voting_Proposal'$1_governance_proposal_GovernanceProposal'(s2))}

// struct voting::RegisterForumEvent at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:151:5+121
type {:datatype} $1_voting_RegisterForumEvent;
function {:constructor} $1_voting_RegisterForumEvent($hosting_account: int, $proposal_type_info: $1_type_info_TypeInfo): $1_voting_RegisterForumEvent;
function {:inline} $Update'$1_voting_RegisterForumEvent'_hosting_account(s: $1_voting_RegisterForumEvent, x: int): $1_voting_RegisterForumEvent {
    $1_voting_RegisterForumEvent(x, $proposal_type_info#$1_voting_RegisterForumEvent(s))
}
function {:inline} $Update'$1_voting_RegisterForumEvent'_proposal_type_info(s: $1_voting_RegisterForumEvent, x: $1_type_info_TypeInfo): $1_voting_RegisterForumEvent {
    $1_voting_RegisterForumEvent($hosting_account#$1_voting_RegisterForumEvent(s), x)
}
function $IsValid'$1_voting_RegisterForumEvent'(s: $1_voting_RegisterForumEvent): bool {
    $IsValid'address'($hosting_account#$1_voting_RegisterForumEvent(s))
      && $IsValid'$1_type_info_TypeInfo'($proposal_type_info#$1_voting_RegisterForumEvent(s))
}
function {:inline} $IsEqual'$1_voting_RegisterForumEvent'(s1: $1_voting_RegisterForumEvent, s2: $1_voting_RegisterForumEvent): bool {
    $IsEqual'address'($hosting_account#$1_voting_RegisterForumEvent(s1), $hosting_account#$1_voting_RegisterForumEvent(s2))
    && $IsEqual'$1_type_info_TypeInfo'($proposal_type_info#$1_voting_RegisterForumEvent(s1), $proposal_type_info#$1_voting_RegisterForumEvent(s2))}

// struct voting::ResolveProposal at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:161:5+150
type {:datatype} $1_voting_ResolveProposal;
function {:constructor} $1_voting_ResolveProposal($proposal_id: int, $yes_votes: int, $no_votes: int, $resolved_early: bool): $1_voting_ResolveProposal;
function {:inline} $Update'$1_voting_ResolveProposal'_proposal_id(s: $1_voting_ResolveProposal, x: int): $1_voting_ResolveProposal {
    $1_voting_ResolveProposal(x, $yes_votes#$1_voting_ResolveProposal(s), $no_votes#$1_voting_ResolveProposal(s), $resolved_early#$1_voting_ResolveProposal(s))
}
function {:inline} $Update'$1_voting_ResolveProposal'_yes_votes(s: $1_voting_ResolveProposal, x: int): $1_voting_ResolveProposal {
    $1_voting_ResolveProposal($proposal_id#$1_voting_ResolveProposal(s), x, $no_votes#$1_voting_ResolveProposal(s), $resolved_early#$1_voting_ResolveProposal(s))
}
function {:inline} $Update'$1_voting_ResolveProposal'_no_votes(s: $1_voting_ResolveProposal, x: int): $1_voting_ResolveProposal {
    $1_voting_ResolveProposal($proposal_id#$1_voting_ResolveProposal(s), $yes_votes#$1_voting_ResolveProposal(s), x, $resolved_early#$1_voting_ResolveProposal(s))
}
function {:inline} $Update'$1_voting_ResolveProposal'_resolved_early(s: $1_voting_ResolveProposal, x: bool): $1_voting_ResolveProposal {
    $1_voting_ResolveProposal($proposal_id#$1_voting_ResolveProposal(s), $yes_votes#$1_voting_ResolveProposal(s), $no_votes#$1_voting_ResolveProposal(s), x)
}
function $IsValid'$1_voting_ResolveProposal'(s: $1_voting_ResolveProposal): bool {
    $IsValid'u64'($proposal_id#$1_voting_ResolveProposal(s))
      && $IsValid'u128'($yes_votes#$1_voting_ResolveProposal(s))
      && $IsValid'u128'($no_votes#$1_voting_ResolveProposal(s))
      && $IsValid'bool'($resolved_early#$1_voting_ResolveProposal(s))
}
function {:inline} $IsEqual'$1_voting_ResolveProposal'(s1: $1_voting_ResolveProposal, s2: $1_voting_ResolveProposal): bool {
    s1 == s2
}

// struct voting::VoteEvent at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:156:5+90
type {:datatype} $1_voting_VoteEvent;
function {:constructor} $1_voting_VoteEvent($proposal_id: int, $num_votes: int): $1_voting_VoteEvent;
function {:inline} $Update'$1_voting_VoteEvent'_proposal_id(s: $1_voting_VoteEvent, x: int): $1_voting_VoteEvent {
    $1_voting_VoteEvent(x, $num_votes#$1_voting_VoteEvent(s))
}
function {:inline} $Update'$1_voting_VoteEvent'_num_votes(s: $1_voting_VoteEvent, x: int): $1_voting_VoteEvent {
    $1_voting_VoteEvent($proposal_id#$1_voting_VoteEvent(s), x)
}
function $IsValid'$1_voting_VoteEvent'(s: $1_voting_VoteEvent): bool {
    $IsValid'u64'($proposal_id#$1_voting_VoteEvent(s))
      && $IsValid'u64'($num_votes#$1_voting_VoteEvent(s))
}
function {:inline} $IsEqual'$1_voting_VoteEvent'(s1: $1_voting_VoteEvent, s2: $1_voting_VoteEvent): bool {
    s1 == s2
}

// struct voting::VotingEvents at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:135:5+275
type {:datatype} $1_voting_VotingEvents;
function {:constructor} $1_voting_VotingEvents($create_proposal_events: $1_event_EventHandle'$1_voting_CreateProposalEvent', $register_forum_events: $1_event_EventHandle'$1_voting_RegisterForumEvent', $resolve_proposal_events: $1_event_EventHandle'$1_voting_ResolveProposal', $vote_events: $1_event_EventHandle'$1_voting_VoteEvent'): $1_voting_VotingEvents;
function {:inline} $Update'$1_voting_VotingEvents'_create_proposal_events(s: $1_voting_VotingEvents, x: $1_event_EventHandle'$1_voting_CreateProposalEvent'): $1_voting_VotingEvents {
    $1_voting_VotingEvents(x, $register_forum_events#$1_voting_VotingEvents(s), $resolve_proposal_events#$1_voting_VotingEvents(s), $vote_events#$1_voting_VotingEvents(s))
}
function {:inline} $Update'$1_voting_VotingEvents'_register_forum_events(s: $1_voting_VotingEvents, x: $1_event_EventHandle'$1_voting_RegisterForumEvent'): $1_voting_VotingEvents {
    $1_voting_VotingEvents($create_proposal_events#$1_voting_VotingEvents(s), x, $resolve_proposal_events#$1_voting_VotingEvents(s), $vote_events#$1_voting_VotingEvents(s))
}
function {:inline} $Update'$1_voting_VotingEvents'_resolve_proposal_events(s: $1_voting_VotingEvents, x: $1_event_EventHandle'$1_voting_ResolveProposal'): $1_voting_VotingEvents {
    $1_voting_VotingEvents($create_proposal_events#$1_voting_VotingEvents(s), $register_forum_events#$1_voting_VotingEvents(s), x, $vote_events#$1_voting_VotingEvents(s))
}
function {:inline} $Update'$1_voting_VotingEvents'_vote_events(s: $1_voting_VotingEvents, x: $1_event_EventHandle'$1_voting_VoteEvent'): $1_voting_VotingEvents {
    $1_voting_VotingEvents($create_proposal_events#$1_voting_VotingEvents(s), $register_forum_events#$1_voting_VotingEvents(s), $resolve_proposal_events#$1_voting_VotingEvents(s), x)
}
function $IsValid'$1_voting_VotingEvents'(s: $1_voting_VotingEvents): bool {
    $IsValid'$1_event_EventHandle'$1_voting_CreateProposalEvent''($create_proposal_events#$1_voting_VotingEvents(s))
      && $IsValid'$1_event_EventHandle'$1_voting_RegisterForumEvent''($register_forum_events#$1_voting_VotingEvents(s))
      && $IsValid'$1_event_EventHandle'$1_voting_ResolveProposal''($resolve_proposal_events#$1_voting_VotingEvents(s))
      && $IsValid'$1_event_EventHandle'$1_voting_VoteEvent''($vote_events#$1_voting_VotingEvents(s))
}
function {:inline} $IsEqual'$1_voting_VotingEvents'(s1: $1_voting_VotingEvents, s2: $1_voting_VotingEvents): bool {
    s1 == s2
}

// struct voting::VotingForum<governance_proposal::GovernanceProposal> at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:126:5+445
type {:datatype} $1_voting_VotingForum'$1_governance_proposal_GovernanceProposal';
function {:constructor} $1_voting_VotingForum'$1_governance_proposal_GovernanceProposal'($proposals: Table int ($1_voting_Proposal'$1_governance_proposal_GovernanceProposal'), $events: $1_voting_VotingEvents, $next_proposal_id: int): $1_voting_VotingForum'$1_governance_proposal_GovernanceProposal';
function {:inline} $Update'$1_voting_VotingForum'$1_governance_proposal_GovernanceProposal''_proposals(s: $1_voting_VotingForum'$1_governance_proposal_GovernanceProposal', x: Table int ($1_voting_Proposal'$1_governance_proposal_GovernanceProposal')): $1_voting_VotingForum'$1_governance_proposal_GovernanceProposal' {
    $1_voting_VotingForum'$1_governance_proposal_GovernanceProposal'(x, $events#$1_voting_VotingForum'$1_governance_proposal_GovernanceProposal'(s), $next_proposal_id#$1_voting_VotingForum'$1_governance_proposal_GovernanceProposal'(s))
}
function {:inline} $Update'$1_voting_VotingForum'$1_governance_proposal_GovernanceProposal''_events(s: $1_voting_VotingForum'$1_governance_proposal_GovernanceProposal', x: $1_voting_VotingEvents): $1_voting_VotingForum'$1_governance_proposal_GovernanceProposal' {
    $1_voting_VotingForum'$1_governance_proposal_GovernanceProposal'($proposals#$1_voting_VotingForum'$1_governance_proposal_GovernanceProposal'(s), x, $next_proposal_id#$1_voting_VotingForum'$1_governance_proposal_GovernanceProposal'(s))
}
function {:inline} $Update'$1_voting_VotingForum'$1_governance_proposal_GovernanceProposal''_next_proposal_id(s: $1_voting_VotingForum'$1_governance_proposal_GovernanceProposal', x: int): $1_voting_VotingForum'$1_governance_proposal_GovernanceProposal' {
    $1_voting_VotingForum'$1_governance_proposal_GovernanceProposal'($proposals#$1_voting_VotingForum'$1_governance_proposal_GovernanceProposal'(s), $events#$1_voting_VotingForum'$1_governance_proposal_GovernanceProposal'(s), x)
}
function $IsValid'$1_voting_VotingForum'$1_governance_proposal_GovernanceProposal''(s: $1_voting_VotingForum'$1_governance_proposal_GovernanceProposal'): bool {
    $IsValid'$1_table_Table'u64_$1_voting_Proposal'$1_governance_proposal_GovernanceProposal'''($proposals#$1_voting_VotingForum'$1_governance_proposal_GovernanceProposal'(s))
      && $IsValid'$1_voting_VotingEvents'($events#$1_voting_VotingForum'$1_governance_proposal_GovernanceProposal'(s))
      && $IsValid'u64'($next_proposal_id#$1_voting_VotingForum'$1_governance_proposal_GovernanceProposal'(s))
}
function {:inline} $IsEqual'$1_voting_VotingForum'$1_governance_proposal_GovernanceProposal''(s1: $1_voting_VotingForum'$1_governance_proposal_GovernanceProposal', s2: $1_voting_VotingForum'$1_governance_proposal_GovernanceProposal'): bool {
    s1 == s2
}
var $1_voting_VotingForum'$1_governance_proposal_GovernanceProposal'_$memory: $Memory $1_voting_VotingForum'$1_governance_proposal_GovernanceProposal';

// fun voting::can_be_resolved_early<governance_proposal::GovernanceProposal> [baseline] at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:507:5+468
procedure {:inline 1} $1_voting_can_be_resolved_early'$1_governance_proposal_GovernanceProposal'(_$t0: $1_voting_Proposal'$1_governance_proposal_GovernanceProposal') returns ($ret0: bool)
{
    // declare local variables
    var $t1: bool;
    var $t2: int;
    var $t3: $1_option_Option'u128';
    var $t4: bool;
    var $t5: $1_option_Option'u128';
    var $t6: int;
    var $t7: bool;
    var $t8: int;
    var $t9: int;
    var $t10: bool;
    var $t11: bool;
    var $t12: int;
    var $t13: bool;
    var $t14: bool;
    var $t15: bool;
    var $t0: $1_voting_Proposal'$1_governance_proposal_GovernanceProposal';
    var $temp_0'$1_voting_Proposal'$1_governance_proposal_GovernanceProposal'': $1_voting_Proposal'$1_governance_proposal_GovernanceProposal';
    var $temp_0'bool': bool;
    var $temp_0'u128': int;
    $t0 := _$t0;

    // bytecode translation starts here
    // trace_local[proposal]($t0) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:507:5+1
    assume {:print "$at(153,27193,27194)"} true;
    assume {:print "$track_local(30,0,0):", $t0} $t0 == $t0;

    // $t3 := get_field<voting::Proposal<#0>>.early_resolution_vote_threshold($t0) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:508:29+41
    assume {:print "$at(153,27318,27359)"} true;
    $t3 := $early_resolution_vote_threshold#$1_voting_Proposal'$1_governance_proposal_GovernanceProposal'($t0);

    // $t4 := opaque begin: option::is_some<u128>($t3) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:508:13+58

    // assume WellFormed($t4) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:508:13+58
    assume $IsValid'bool'($t4);

    // assume Eq<bool>($t4, option::spec_is_some<u128>($t3)) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:508:13+58
    assume $IsEqual'bool'($t4, $1_option_spec_is_some'u128'($t3));

    // $t4 := opaque end: option::is_some<u128>($t3) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:508:13+58

    // if ($t4) goto L1 else goto L0 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:508:9+342
    if ($t4) { goto L1; } else { goto L0; }

    // label L1 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:509:63+8
    assume {:print "$at(153,27426,27434)"} true;
L1:

    // $t5 := get_field<voting::Proposal<#0>>.early_resolution_vote_threshold($t0) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:509:62+41
    assume {:print "$at(153,27425,27466)"} true;
    $t5 := $early_resolution_vote_threshold#$1_voting_Proposal'$1_governance_proposal_GovernanceProposal'($t0);

    // $t6 := opaque begin: option::borrow<u128>($t5) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:509:47+57

    // assume Identical($t7, option::spec_is_none<u128>($t5)) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:509:47+57
    assume ($t7 == $1_option_spec_is_none'u128'($t5));

    // if ($t7) goto L11 else goto L10 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:509:47+57
    if ($t7) { goto L11; } else { goto L10; }

    // label L11 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:509:47+57
L11:

    // assume And(option::spec_is_none<u128>($t5), Eq(262145, $t8)) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:509:47+57
    assume {:print "$at(153,27410,27467)"} true;
    assume ($1_option_spec_is_none'u128'($t5) && $IsEqual'num'(262145, $t8));

    // trace_abort($t8) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:509:47+57
    assume {:print "$at(153,27410,27467)"} true;
    assume {:print "$track_abort(30,0):", $t8} $t8 == $t8;

    // goto L9 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:509:47+57
    goto L9;

    // label L10 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:509:47+57
L10:

    // assume WellFormed($t6) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:509:47+57
    assume {:print "$at(153,27410,27467)"} true;
    assume $IsValid'u128'($t6);

    // assume Eq<u128>($t6, option::spec_borrow<u128>($t5)) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:509:47+57
    assume $IsEqual'u128'($t6, $1_option_spec_borrow'u128'($t5));

    // $t6 := opaque end: option::borrow<u128>($t5) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:509:47+57

    // trace_local[early_resolution_threshold]($t6) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:509:17+26
    assume {:print "$track_local(30,0,2):", $t6} $t6 == $t6;

    // $t9 := get_field<voting::Proposal<#0>>.yes_votes($t0) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:510:17+18
    assume {:print "$at(153,27485,27503)"} true;
    $t9 := $yes_votes#$1_voting_Proposal'$1_governance_proposal_GovernanceProposal'($t0);

    // $t10 := >=($t9, $t6) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:510:36+2
    call $t10 := $Ge($t9, $t6);

    // if ($t10) goto L3 else goto L2 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:510:17+99
    if ($t10) { goto L3; } else { goto L2; }

    // label L3 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:510:17+99
L3:

    // $t11 := true at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:510:17+99
    assume {:print "$at(153,27485,27584)"} true;
    $t11 := true;
    assume $IsValid'bool'($t11);

    // $t1 := $t11 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:510:17+99
    $t1 := $t11;

    // goto L4 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:510:17+99
    goto L4;

    // label L2 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:510:69+8
L2:

    // $t12 := get_field<voting::Proposal<#0>>.no_votes($t0) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:510:69+17
    assume {:print "$at(153,27537,27554)"} true;
    $t12 := $no_votes#$1_voting_Proposal'$1_governance_proposal_GovernanceProposal'($t0);

    // $t1 := >=($t12, $t6) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:510:87+2
    call $t1 := $Ge($t12, $t6);

    // label L4 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:510:17+99
L4:

    // if ($t1) goto L6 else goto L5 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:510:13+148
    assume {:print "$at(153,27481,27629)"} true;
    if ($t1) { goto L6; } else { goto L5; }

    // label L6 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:511:24+4
    assume {:print "$at(153,27611,27615)"} true;
L6:

    // $t13 := true at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:511:24+4
    assume {:print "$at(153,27611,27615)"} true;
    $t13 := true;
    assume $IsValid'bool'($t13);

    // trace_return[0]($t13) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:511:17+11
    assume {:print "$track_return(30,0,0):", $t13} $t13 == $t13;

    // $t14 := move($t13) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:511:17+11
    $t14 := $t13;

    // goto L8 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:511:17+11
    goto L8;

    // label L5 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:512:14+1
    assume {:print "$at(153,27629,27630)"} true;
L5:

    // goto L7 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:512:14+1
    assume {:print "$at(153,27629,27630)"} true;
    goto L7;

    // label L0 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:508:9+342
    assume {:print "$at(153,27298,27640)"} true;
L0:

    // label L7 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:514:9+5
    assume {:print "$at(153,27650,27655)"} true;
L7:

    // $t15 := false at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:514:9+5
    assume {:print "$at(153,27650,27655)"} true;
    $t15 := false;
    assume $IsValid'bool'($t15);

    // trace_return[0]($t15) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:514:9+5
    assume {:print "$track_return(30,0,0):", $t15} $t15 == $t15;

    // $t14 := move($t15) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:514:9+5
    $t14 := $t15;

    // label L8 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:515:5+1
    assume {:print "$at(153,27660,27661)"} true;
L8:

    // return $t14 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:515:5+1
    assume {:print "$at(153,27660,27661)"} true;
    $ret0 := $t14;
    return;

    // label L9 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:515:5+1
L9:

    // abort($t8) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:515:5+1
    assume {:print "$at(153,27660,27661)"} true;
    $abort_code := $t8;
    $abort_flag := true;
    return;

}

// fun voting::get_execution_hash<governance_proposal::GovernanceProposal> [baseline] at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:567:5+362
procedure {:inline 1} $1_voting_get_execution_hash'$1_governance_proposal_GovernanceProposal'(_$t0: int, _$t1: int) returns ($ret0: Vec (int))
{
    // declare local variables
    var $t2: $1_voting_VotingForum'$1_governance_proposal_GovernanceProposal';
    var $t3: $1_voting_VotingForum'$1_governance_proposal_GovernanceProposal';
    var $t4: int;
    var $t5: Table int ($1_voting_Proposal'$1_governance_proposal_GovernanceProposal');
    var $t6: $1_voting_Proposal'$1_governance_proposal_GovernanceProposal';
    var $t7: Vec (int);
    var $t0: int;
    var $t1: int;
    var $temp_0'address': int;
    var $temp_0'u64': int;
    var $temp_0'vec'u8'': Vec (int);
    $t0 := _$t0;
    $t1 := _$t1;

    // bytecode translation starts here
    // assume Identical($t2, global<voting::VotingForum<#0>>($t0)) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.spec.move:286:9+75
    assume {:print "$at(154,12822,12897)"} true;
    assume ($t2 == $ResourceValue($1_voting_VotingForum'$1_governance_proposal_GovernanceProposal'_$memory, $t0));

    // trace_local[voting_forum_address]($t0) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:567:5+1
    assume {:print "$at(153,29632,29633)"} true;
    assume {:print "$track_local(30,4,0):", $t0} $t0 == $t0;

    // trace_local[proposal_id]($t1) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:567:5+1
    assume {:print "$track_local(30,4,1):", $t1} $t1 == $t1;

    // $t3 := get_global<voting::VotingForum<#0>>($t0) on_abort goto L2 with $t4 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:571:28+13
    assume {:print "$at(153,29817,29830)"} true;
    if (!$ResourceExists($1_voting_VotingForum'$1_governance_proposal_GovernanceProposal'_$memory, $t0)) {
        call $ExecFailureAbort();
    } else {
        $t3 := $ResourceValue($1_voting_VotingForum'$1_governance_proposal_GovernanceProposal'_$memory, $t0);
    }
    if ($abort_flag) {
        assume {:print "$at(153,29817,29830)"} true;
        $t4 := $abort_code;
        assume {:print "$track_abort(30,4):", $t4} $t4 == $t4;
        goto L2;
    }

    // $t5 := get_field<voting::VotingForum<#0>>.proposals($t3) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:572:38+23
    assume {:print "$at(153,29918,29941)"} true;
    $t5 := $proposals#$1_voting_VotingForum'$1_governance_proposal_GovernanceProposal'($t3);

    // $t6 := table::borrow<u64, voting::Proposal<#0>>($t5, $t1) on_abort goto L2 with $t4 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:572:24+51
    call $t6 := $1_table_borrow'u64_$1_voting_Proposal'$1_governance_proposal_GovernanceProposal''($t5, $t1);
    if ($abort_flag) {
        assume {:print "$at(153,29904,29955)"} true;
        $t4 := $abort_code;
        assume {:print "$track_abort(30,4):", $t4} $t4 == $t4;
        goto L2;
    }

    // $t7 := get_field<voting::Proposal<#0>>.execution_hash($t6) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:573:9+23
    assume {:print "$at(153,29965,29988)"} true;
    $t7 := $execution_hash#$1_voting_Proposal'$1_governance_proposal_GovernanceProposal'($t6);

    // trace_return[0]($t7) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:573:9+23
    assume {:print "$track_return(30,4,0):", $t7} $t7 == $t7;

    // label L1 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:574:5+1
    assume {:print "$at(153,29993,29994)"} true;
L1:

    // return $t7 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:574:5+1
    assume {:print "$at(153,29993,29994)"} true;
    $ret0 := $t7;
    return;

    // label L2 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:574:5+1
L2:

    // abort($t4) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:574:5+1
    assume {:print "$at(153,29993,29994)"} true;
    $abort_code := $t4;
    $abort_flag := true;
    return;

}

// fun voting::get_proposal_state<governance_proposal::GovernanceProposal> [baseline] at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:523:5+778
procedure {:inline 1} $1_voting_get_proposal_state'$1_governance_proposal_GovernanceProposal'(_$t0: int, _$t1: int) returns ($ret0: int)
{
    // declare local variables
    var $t2: bool;
    var $t3: int;
    var $t4: int;
    var $t5: int;
    var $t6: $1_voting_Proposal'$1_governance_proposal_GovernanceProposal';
    var $t7: int;
    var $t8: $1_voting_VotingForum'$1_governance_proposal_GovernanceProposal';
    var $t9: $1_voting_Proposal'$1_governance_proposal_GovernanceProposal';
    var $t10: int;
    var $t11: bool;
    var $t12: bool;
    var $t13: bool;
    var $t14: $1_voting_VotingForum'$1_governance_proposal_GovernanceProposal';
    var $t15: $1_voting_VotingForum'$1_governance_proposal_GovernanceProposal';
    var $t16: bool;
    var $t17: int;
    var $t18: $1_voting_VotingForum'$1_governance_proposal_GovernanceProposal';
    var $t19: Table int ($1_voting_Proposal'$1_governance_proposal_GovernanceProposal');
    var $t20: $1_voting_Proposal'$1_governance_proposal_GovernanceProposal';
    var $t21: int;
    var $t22: int;
    var $t23: bool;
    var $t24: int;
    var $t25: int;
    var $t26: bool;
    var $t27: int;
    var $t28: int;
    var $t29: int;
    var $t0: int;
    var $t1: int;
    var $temp_0'$1_voting_Proposal'$1_governance_proposal_GovernanceProposal'': $1_voting_Proposal'$1_governance_proposal_GovernanceProposal';
    var $temp_0'address': int;
    var $temp_0'u128': int;
    var $temp_0'u64': int;
    $t0 := _$t0;
    $t1 := _$t1;

    // bytecode translation starts here
    // assume Identical($t8, global<voting::VotingForum<#0>>($t0)) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.spec.move:212:9+75
    assume {:print "$at(154,9952,10027)"} true;
    assume ($t8 == $ResourceValue($1_voting_VotingForum'$1_governance_proposal_GovernanceProposal'_$memory, $t0));

    // assume Identical($t9, table::spec_get<u64, voting::Proposal<#0>>(select voting::VotingForum.proposals($t8), $t1)) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.spec.move:213:9+68
    assume {:print "$at(154,10036,10104)"} true;
    assume ($t9 == $1_table_spec_get'u64_$1_voting_Proposal'$1_governance_proposal_GovernanceProposal''($proposals#$1_voting_VotingForum'$1_governance_proposal_GovernanceProposal'($t8), $t1));

    // assume Identical($t10, option::spec_borrow<u128>(select voting::Proposal.early_resolution_vote_threshold($t9))) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.spec.move:214:9+95
    assume {:print "$at(154,10113,10208)"} true;
    assume ($t10 == $1_option_spec_borrow'u128'($early_resolution_vote_threshold#$1_voting_Proposal'$1_governance_proposal_GovernanceProposal'($t9)));

    // assume Identical($t11, Gt(timestamp::$now_seconds(), select voting::Proposal.expiration_secs($t9))) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.spec.move:215:9+77
    assume {:print "$at(154,10217,10294)"} true;
    assume ($t11 == ($1_timestamp_$now_seconds($1_timestamp_CurrentTimeMicroseconds_$memory) > $expiration_secs#$1_voting_Proposal'$1_governance_proposal_GovernanceProposal'($t9)));

    // assume Identical($t12, And(option::spec_is_some<u128>(select voting::Proposal.early_resolution_vote_threshold($t9)), Or(Ge(select voting::Proposal.yes_votes($t9), $t10), Ge(select voting::Proposal.no_votes($t9), $t10)))) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.spec.move:216:9+266
    assume {:print "$at(154,10303,10569)"} true;
    assume ($t12 == ($1_option_spec_is_some'u128'($early_resolution_vote_threshold#$1_voting_Proposal'$1_governance_proposal_GovernanceProposal'($t9)) && (($yes_votes#$1_voting_Proposal'$1_governance_proposal_GovernanceProposal'($t9) >= $t10) || ($no_votes#$1_voting_Proposal'$1_governance_proposal_GovernanceProposal'($t9) >= $t10))));

    // assume Identical($t13, Or($t11, $t12)) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.spec.move:219:9+60
    assume {:print "$at(154,10578,10638)"} true;
    assume ($t13 == ($t11 || $t12));

    // assume Identical($t14, global<voting::VotingForum<#0>>($t0)) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.spec.move:286:9+75
    assume {:print "$at(154,12822,12897)"} true;
    assume ($t14 == $ResourceValue($1_voting_VotingForum'$1_governance_proposal_GovernanceProposal'_$memory, $t0));

    // assume chain_status::$is_operating() at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.spec.move:208:9+38
    assume {:print "$at(154,9809,9847)"} true;
    assume $1_chain_status_$is_operating($1_chain_status_GenesisEndMarker_$memory);

    // trace_local[voting_forum_address]($t0) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:523:5+1
    assume {:print "$at(153,27929,27930)"} true;
    assume {:print "$track_local(30,8,0):", $t0} $t0 == $t0;

    // trace_local[proposal_id]($t1) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:523:5+1
    assume {:print "$track_local(30,8,1):", $t1} $t1 == $t1;

    // assume Identical($t15, global<voting::VotingForum<#0>>($t0)) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.spec.move:286:9+75
    assume {:print "$at(154,12822,12897)"} true;
    assume ($t15 == $ResourceValue($1_voting_VotingForum'$1_governance_proposal_GovernanceProposal'_$memory, $t0));

    // $t16 := voting::is_voting_closed<#0>($t0, $t1) on_abort goto L10 with $t17 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:527:13+65
    assume {:print "$at(153,28092,28157)"} true;
    call $t16 := $1_voting_is_voting_closed'$1_governance_proposal_GovernanceProposal'($t0, $t1);
    if ($abort_flag) {
        assume {:print "$at(153,28092,28157)"} true;
        $t17 := $abort_code;
        assume {:print "$track_abort(30,8):", $t17} $t17 == $t17;
        goto L10;
    }

    // if ($t16) goto L1 else goto L0 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:527:9+613
    if ($t16) { goto L1; } else { goto L0; }

    // label L1 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:528:73+20
    assume {:print "$at(153,28233,28253)"} true;
L1:

    // $t18 := get_global<voting::VotingForum<#0>>($t0) on_abort goto L10 with $t17 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:528:32+13
    assume {:print "$at(153,28192,28205)"} true;
    if (!$ResourceExists($1_voting_VotingForum'$1_governance_proposal_GovernanceProposal'_$memory, $t0)) {
        call $ExecFailureAbort();
    } else {
        $t18 := $ResourceValue($1_voting_VotingForum'$1_governance_proposal_GovernanceProposal'_$memory, $t0);
    }
    if ($abort_flag) {
        assume {:print "$at(153,28192,28205)"} true;
        $t17 := $abort_code;
        assume {:print "$track_abort(30,8):", $t17} $t17 == $t17;
        goto L10;
    }

    // $t19 := get_field<voting::VotingForum<#0>>.proposals($t18) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:529:42+23
    assume {:print "$at(153,28297,28320)"} true;
    $t19 := $proposals#$1_voting_VotingForum'$1_governance_proposal_GovernanceProposal'($t18);

    // $t20 := table::borrow<u64, voting::Proposal<#0>>($t19, $t1) on_abort goto L10 with $t17 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:529:28+51
    call $t20 := $1_table_borrow'u64_$1_voting_Proposal'$1_governance_proposal_GovernanceProposal''($t19, $t1);
    if ($abort_flag) {
        assume {:print "$at(153,28283,28334)"} true;
        $t17 := $abort_code;
        assume {:print "$track_abort(30,8):", $t17} $t17 == $t17;
        goto L10;
    }

    // trace_local[proposal]($t20) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:529:17+8
    assume {:print "$track_local(30,8,6):", $t20} $t20 == $t20;

    // $t21 := get_field<voting::Proposal<#0>>.yes_votes($t20) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:530:29+18
    assume {:print "$at(153,28364,28382)"} true;
    $t21 := $yes_votes#$1_voting_Proposal'$1_governance_proposal_GovernanceProposal'($t20);

    // trace_local[yes_votes]($t21) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:530:17+9
    assume {:print "$track_local(30,8,7):", $t21} $t21 == $t21;

    // $t22 := get_field<voting::Proposal<#0>>.no_votes($t20) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:531:28+17
    assume {:print "$at(153,28411,28428)"} true;
    $t22 := $no_votes#$1_voting_Proposal'$1_governance_proposal_GovernanceProposal'($t20);

    // trace_local[no_votes]($t22) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:531:17+8
    assume {:print "$track_local(30,8,5):", $t22} $t22 == $t22;

    // $t23 := >($t21, $t22) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:533:27+1
    assume {:print "$at(153,28457,28458)"} true;
    call $t23 := $Gt($t21, $t22);

    // if ($t23) goto L3 else goto L2 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:533:17+75
    if ($t23) { goto L3; } else { goto L2; }

    // label L3 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:533:41+9
L3:

    // $t24 := +($t21, $t22) on_abort goto L10 with $t17 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:533:51+1
    assume {:print "$at(153,28481,28482)"} true;
    call $t24 := $AddU128_unchecked($t21, $t22);
    if ($abort_flag) {
        assume {:print "$at(153,28481,28482)"} true;
        $t17 := $abort_code;
        assume {:print "$track_abort(30,8):", $t17} $t17 == $t17;
        goto L10;
    }

    // $t25 := get_field<voting::Proposal<#0>>.min_vote_threshold($t20) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:533:65+27
    $t25 := $min_vote_threshold#$1_voting_Proposal'$1_governance_proposal_GovernanceProposal'($t20);

    // $t2 := >=($t24, $t25) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:533:62+2
    call $t2 := $Ge($t24, $t25);

    // goto L4 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:533:17+75
    goto L4;

    // label L2 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:533:17+75
L2:

    // $t26 := false at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:533:17+75
    assume {:print "$at(153,28447,28522)"} true;
    $t26 := false;
    assume $IsValid'bool'($t26);

    // $t2 := $t26 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:533:17+75
    $t2 := $t26;

    // label L4 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:533:17+75
L4:

    // if ($t2) goto L6 else goto L5 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:533:13+196
    assume {:print "$at(153,28443,28639)"} true;
    if ($t2) { goto L6; } else { goto L5; }

    // label L6 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:534:17+24
    assume {:print "$at(153,28542,28566)"} true;
L6:

    // $t27 := 1 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:534:17+24
    assume {:print "$at(153,28542,28566)"} true;
    $t27 := 1;
    assume $IsValid'u64'($t27);

    // $t3 := $t27 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:533:13+196
    assume {:print "$at(153,28443,28639)"} true;
    $t3 := $t27;

    // goto L7 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:533:13+196
    goto L7;

    // label L5 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:536:17+21
    assume {:print "$at(153,28604,28625)"} true;
L5:

    // $t28 := 3 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:536:17+21
    assume {:print "$at(153,28604,28625)"} true;
    $t28 := 3;
    assume $IsValid'u64'($t28);

    // $t3 := $t28 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:533:13+196
    assume {:print "$at(153,28443,28639)"} true;
    $t3 := $t28;

    // label L7 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:533:13+196
L7:

    // $t4 := $t3 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:527:9+613
    assume {:print "$at(153,28088,28701)"} true;
    $t4 := $t3;

    // goto L8 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:527:9+613
    goto L8;

    // label L0 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:539:13+22
    assume {:print "$at(153,28669,28691)"} true;
L0:

    // $t29 := 0 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:539:13+22
    assume {:print "$at(153,28669,28691)"} true;
    $t29 := 0;
    assume $IsValid'u64'($t29);

    // $t4 := $t29 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:527:9+613
    assume {:print "$at(153,28088,28701)"} true;
    $t4 := $t29;

    // label L8 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:527:9+613
L8:

    // trace_return[0]($t4) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:527:9+613
    assume {:print "$at(153,28088,28701)"} true;
    assume {:print "$track_return(30,8,0):", $t4} $t4 == $t4;

    // label L9 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:541:5+1
    assume {:print "$at(153,28706,28707)"} true;
L9:

    // return $t4 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:541:5+1
    assume {:print "$at(153,28706,28707)"} true;
    $ret0 := $t4;
    return;

    // label L10 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:541:5+1
L10:

    // abort($t17) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:541:5+1
    assume {:print "$at(153,28706,28707)"} true;
    $abort_code := $t17;
    $abort_flag := true;
    return;

}

// fun voting::is_proposal_resolvable<governance_proposal::GovernanceProposal> [baseline] at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:365:5+1214
procedure {:inline 1} $1_voting_is_proposal_resolvable'$1_governance_proposal_GovernanceProposal'(_$t0: int, _$t1: int) returns ()
{
    // declare local variables
    var $t2: $1_string_String;
    var $t3: Table int (Vec (int));
    var $t4: $Mutation ($1_voting_Proposal'$1_governance_proposal_GovernanceProposal');
    var $t5: int;
    var $t6: $1_voting_VotingForum'$1_governance_proposal_GovernanceProposal';
    var $t7: $1_voting_Proposal'$1_governance_proposal_GovernanceProposal';
    var $t8: int;
    var $t9: bool;
    var $t10: bool;
    var $t11: bool;
    var $t12: $1_voting_VotingForum'$1_governance_proposal_GovernanceProposal';
    var $t13: $1_voting_VotingForum'$1_governance_proposal_GovernanceProposal';
    var $t14: $1_voting_Proposal'$1_governance_proposal_GovernanceProposal';
    var $t15: int;
    var $t16: bool;
    var $t17: bool;
    var $t18: bool;
    var $t19: $1_voting_VotingForum'$1_governance_proposal_GovernanceProposal';
    var $t20: int;
    var $t21: int;
    var $t22: int;
    var $t23: bool;
    var $t24: int;
    var $t25: int;
    var $t26: $Mutation ($1_voting_VotingForum'$1_governance_proposal_GovernanceProposal');
    var $t27: $Mutation (Table int ($1_voting_Proposal'$1_governance_proposal_GovernanceProposal'));
    var $t28: $Mutation ($1_voting_Proposal'$1_governance_proposal_GovernanceProposal');
    var $t29: bool;
    var $t30: bool;
    var $t31: int;
    var $t32: int;
    var $t33: Table int (Vec (int));
    var $t34: Vec (int);
    var $t35: $1_string_String;
    var $t36: Vec (int);
    var $t37: int;
    var $t38: int;
    var $t39: bool;
    var $t40: int;
    var $t41: int;
    var $t42: Vec (int);
    var $t43: Vec (int);
    var $t44: bool;
    var $t45: int;
    var $t46: int;
    var $t0: int;
    var $t1: int;
    var $temp_0'$1_voting_Proposal'$1_governance_proposal_GovernanceProposal'': $1_voting_Proposal'$1_governance_proposal_GovernanceProposal';
    var $temp_0'address': int;
    var $temp_0'u64': int;
    $t0 := _$t0;
    $t1 := _$t1;

    // bytecode translation starts here
    // assume Identical($t6, global<voting::VotingForum<#0>>($t0)) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.spec.move:124:9+75
    assume {:print "$at(154,5795,5870)"} true;
    assume ($t6 == $ResourceValue($1_voting_VotingForum'$1_governance_proposal_GovernanceProposal'_$memory, $t0));

    // assume Identical($t7, table::spec_get<u64, voting::Proposal<#0>>(select voting::VotingForum.proposals($t6), $t1)) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.spec.move:125:9+68
    assume {:print "$at(154,5879,5947)"} true;
    assume ($t7 == $1_table_spec_get'u64_$1_voting_Proposal'$1_governance_proposal_GovernanceProposal''($proposals#$1_voting_VotingForum'$1_governance_proposal_GovernanceProposal'($t6), $t1));

    // assume Identical($t8, option::spec_borrow<u128>(select voting::Proposal.early_resolution_vote_threshold($t7))) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.spec.move:126:9+95
    assume {:print "$at(154,5956,6051)"} true;
    assume ($t8 == $1_option_spec_borrow'u128'($early_resolution_vote_threshold#$1_voting_Proposal'$1_governance_proposal_GovernanceProposal'($t7)));

    // assume Identical($t9, Gt(timestamp::$now_seconds(), select voting::Proposal.expiration_secs($t7))) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.spec.move:127:9+77
    assume {:print "$at(154,6060,6137)"} true;
    assume ($t9 == ($1_timestamp_$now_seconds($1_timestamp_CurrentTimeMicroseconds_$memory) > $expiration_secs#$1_voting_Proposal'$1_governance_proposal_GovernanceProposal'($t7)));

    // assume Identical($t10, And(option::spec_is_some<u128>(select voting::Proposal.early_resolution_vote_threshold($t7)), Or(Ge(select voting::Proposal.yes_votes($t7), $t8), Ge(select voting::Proposal.no_votes($t7), $t8)))) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.spec.move:128:9+266
    assume {:print "$at(154,6146,6412)"} true;
    assume ($t10 == ($1_option_spec_is_some'u128'($early_resolution_vote_threshold#$1_voting_Proposal'$1_governance_proposal_GovernanceProposal'($t7)) && (($yes_votes#$1_voting_Proposal'$1_governance_proposal_GovernanceProposal'($t7) >= $t8) || ($no_votes#$1_voting_Proposal'$1_governance_proposal_GovernanceProposal'($t7) >= $t8))));

    // assume Identical($t11, Or($t9, $t10)) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.spec.move:131:9+60
    assume {:print "$at(154,6421,6481)"} true;
    assume ($t11 == ($t9 || $t10));

    // assume Identical($t12, global<voting::VotingForum<#0>>($t0)) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.spec.move:286:9+75
    assume {:print "$at(154,12822,12897)"} true;
    assume ($t12 == $ResourceValue($1_voting_VotingForum'$1_governance_proposal_GovernanceProposal'_$memory, $t0));

    // assume chain_status::$is_operating() at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.spec.move:120:9+38
    assume {:print "$at(154,5577,5615)"} true;
    assume $1_chain_status_$is_operating($1_chain_status_GenesisEndMarker_$memory);

    // trace_local[voting_forum_address]($t0) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:365:5+1
    assume {:print "$at(153,19448,19449)"} true;
    assume {:print "$track_local(30,11,0):", $t0} $t0 == $t0;

    // trace_local[proposal_id]($t1) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:365:5+1
    assume {:print "$track_local(30,11,1):", $t1} $t1 == $t1;

    // assume Identical($t13, global<voting::VotingForum<#0>>($t0)) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.spec.move:212:9+75
    assume {:print "$at(154,9952,10027)"} true;
    assume ($t13 == $ResourceValue($1_voting_VotingForum'$1_governance_proposal_GovernanceProposal'_$memory, $t0));

    // assume Identical($t14, table::spec_get<u64, voting::Proposal<#0>>(select voting::VotingForum.proposals($t13), $t1)) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.spec.move:213:9+68
    assume {:print "$at(154,10036,10104)"} true;
    assume ($t14 == $1_table_spec_get'u64_$1_voting_Proposal'$1_governance_proposal_GovernanceProposal''($proposals#$1_voting_VotingForum'$1_governance_proposal_GovernanceProposal'($t13), $t1));

    // assume Identical($t15, option::spec_borrow<u128>(select voting::Proposal.early_resolution_vote_threshold($t14))) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.spec.move:214:9+95
    assume {:print "$at(154,10113,10208)"} true;
    assume ($t15 == $1_option_spec_borrow'u128'($early_resolution_vote_threshold#$1_voting_Proposal'$1_governance_proposal_GovernanceProposal'($t14)));

    // assume Identical($t16, Gt(timestamp::$now_seconds(), select voting::Proposal.expiration_secs($t14))) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.spec.move:215:9+77
    assume {:print "$at(154,10217,10294)"} true;
    assume ($t16 == ($1_timestamp_$now_seconds($1_timestamp_CurrentTimeMicroseconds_$memory) > $expiration_secs#$1_voting_Proposal'$1_governance_proposal_GovernanceProposal'($t14)));

    // assume Identical($t17, And(option::spec_is_some<u128>(select voting::Proposal.early_resolution_vote_threshold($t14)), Or(Ge(select voting::Proposal.yes_votes($t14), $t15), Ge(select voting::Proposal.no_votes($t14), $t15)))) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.spec.move:216:9+266
    assume {:print "$at(154,10303,10569)"} true;
    assume ($t17 == ($1_option_spec_is_some'u128'($early_resolution_vote_threshold#$1_voting_Proposal'$1_governance_proposal_GovernanceProposal'($t14)) && (($yes_votes#$1_voting_Proposal'$1_governance_proposal_GovernanceProposal'($t14) >= $t15) || ($no_votes#$1_voting_Proposal'$1_governance_proposal_GovernanceProposal'($t14) >= $t15))));

    // assume Identical($t18, Or($t16, $t17)) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.spec.move:219:9+60
    assume {:print "$at(154,10578,10638)"} true;
    assume ($t18 == ($t16 || $t17));

    // assume Identical($t19, global<voting::VotingForum<#0>>($t0)) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.spec.move:286:9+75
    assume {:print "$at(154,12822,12897)"} true;
    assume ($t19 == $ResourceValue($1_voting_VotingForum'$1_governance_proposal_GovernanceProposal'_$memory, $t0));

    // $t20 := voting::get_proposal_state<#0>($t0, $t1) on_abort goto L13 with $t21 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:369:30+67
    assume {:print "$at(153,19620,19687)"} true;
    call $t20 := $1_voting_get_proposal_state'$1_governance_proposal_GovernanceProposal'($t0, $t1);
    if ($abort_flag) {
        assume {:print "$at(153,19620,19687)"} true;
        $t21 := $abort_code;
        assume {:print "$track_abort(30,11):", $t21} $t21 == $t21;
        goto L13;
    }

    // $t22 := 1 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:370:35+24
    assume {:print "$at(153,19723,19747)"} true;
    $t22 := 1;
    assume $IsValid'u64'($t22);

    // $t23 := ==($t20, $t22) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:370:32+2
    $t23 := $IsEqual'u64'($t20, $t22);

    // if ($t23) goto L1 else goto L0 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:370:9+103
    if ($t23) { goto L1; } else { goto L0; }

    // label L1 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:370:9+103
L1:

    // goto L2 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:370:9+103
    assume {:print "$at(153,19697,19800)"} true;
    goto L2;

    // label L0 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:370:82+28
L0:

    // $t24 := 2 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:370:82+28
    assume {:print "$at(153,19770,19798)"} true;
    $t24 := 2;
    assume $IsValid'u64'($t24);

    // $t25 := error::invalid_state($t24) on_abort goto L13 with $t21 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:370:61+50
    call $t25 := $1_error_invalid_state($t24);
    if ($abort_flag) {
        assume {:print "$at(153,19749,19799)"} true;
        $t21 := $abort_code;
        assume {:print "$track_abort(30,11):", $t21} $t21 == $t21;
        goto L13;
    }

    // trace_abort($t25) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:370:9+103
    assume {:print "$at(153,19697,19800)"} true;
    assume {:print "$track_abort(30,11):", $t25} $t25 == $t25;

    // $t21 := move($t25) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:370:9+103
    $t21 := $t25;

    // goto L13 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:370:9+103
    goto L13;

    // label L2 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:372:73+20
    assume {:print "$at(153,19875,19895)"} true;
L2:

    // $t26 := borrow_global<voting::VotingForum<#0>>($t0) on_abort goto L13 with $t21 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:372:28+17
    assume {:print "$at(153,19830,19847)"} true;
    if (!$ResourceExists($1_voting_VotingForum'$1_governance_proposal_GovernanceProposal'_$memory, $t0)) {
        call $ExecFailureAbort();
    } else {
        $t26 := $Mutation($Global($t0), EmptyVec(), $ResourceValue($1_voting_VotingForum'$1_governance_proposal_GovernanceProposal'_$memory, $t0));
    }
    if ($abort_flag) {
        assume {:print "$at(153,19830,19847)"} true;
        $t21 := $abort_code;
        assume {:print "$track_abort(30,11):", $t21} $t21 == $t21;
        goto L13;
    }

    // $t27 := borrow_field<voting::VotingForum<#0>>.proposals($t26) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:373:42+27
    assume {:print "$at(153,19939,19966)"} true;
    $t27 := $ChildMutation($t26, 0, $proposals#$1_voting_VotingForum'$1_governance_proposal_GovernanceProposal'($Dereference($t26)));

    // $t28 := table::borrow_mut<u64, voting::Proposal<#0>>($t27, $t1) on_abort goto L13 with $t21 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:373:24+59
    call $t28,$t27 := $1_table_borrow_mut'u64_$1_voting_Proposal'$1_governance_proposal_GovernanceProposal''($t27, $t1);
    if ($abort_flag) {
        assume {:print "$at(153,19921,19980)"} true;
        $t21 := $abort_code;
        assume {:print "$track_abort(30,11):", $t21} $t21 == $t21;
        goto L13;
    }

    // trace_local[proposal]($t28) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:373:13+8
    $temp_0'$1_voting_Proposal'$1_governance_proposal_GovernanceProposal'' := $Dereference($t28);
    assume {:print "$track_local(30,11,4):", $temp_0'$1_voting_Proposal'$1_governance_proposal_GovernanceProposal''} $temp_0'$1_voting_Proposal'$1_governance_proposal_GovernanceProposal'' == $temp_0'$1_voting_Proposal'$1_governance_proposal_GovernanceProposal'';

    // $t29 := get_field<voting::Proposal<#0>>.is_resolved($t28) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:374:18+20
    assume {:print "$at(153,19999,20019)"} true;
    $t29 := $is_resolved#$1_voting_Proposal'$1_governance_proposal_GovernanceProposal'($Dereference($t28));

    // $t30 := !($t29) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:374:17+1
    call $t30 := $Not($t29);

    // if ($t30) goto L4 else goto L3 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:374:9+80
    if ($t30) { goto L4; } else { goto L3; }

    // label L4 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:374:9+80
L4:

    // goto L5 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:374:9+80
    assume {:print "$at(153,19990,20070)"} true;
    goto L5;

    // label L3 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:374:9+80
L3:

    // pack_ref_deep($t26) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:374:9+80
    assume {:print "$at(153,19990,20070)"} true;

    // destroy($t28) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:374:9+80

    // $t31 := 3 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:374:61+26
    $t31 := 3;
    assume $IsValid'u64'($t31);

    // $t32 := error::invalid_state($t31) on_abort goto L13 with $t21 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:374:40+48
    call $t32 := $1_error_invalid_state($t31);
    if ($abort_flag) {
        assume {:print "$at(153,20021,20069)"} true;
        $t21 := $abort_code;
        assume {:print "$track_abort(30,11):", $t21} $t21 == $t21;
        goto L13;
    }

    // trace_abort($t32) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:374:9+80
    assume {:print "$at(153,19990,20070)"} true;
    assume {:print "$track_abort(30,11):", $t32} $t32 == $t32;

    // $t21 := move($t32) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:374:9+80
    $t21 := $t32;

    // goto L13 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:374:9+80
    goto L13;

    // label L5 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:378:59+8
    assume {:print "$at(153,20302,20310)"} true;
L5:

    // $t33 := get_field<voting::Proposal<#0>>.metadata($t28) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:378:58+18
    assume {:print "$at(153,20301,20319)"} true;
    $t33 := $metadata#$1_voting_Proposal'$1_governance_proposal_GovernanceProposal'($Dereference($t28));

    // $t34 := [82, 69, 83, 79, 76, 86, 65, 66, 76, 69, 95, 84, 73, 77, 69, 95, 77, 69, 84, 65, 68, 65, 84, 65, 95, 75, 69, 89] at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:378:84+28
    $t34 := ConcatVec(ConcatVec(ConcatVec(ConcatVec(ConcatVec(ConcatVec(MakeVec4(82, 69, 83, 79), MakeVec4(76, 86, 65, 66)), MakeVec4(76, 69, 95, 84)), MakeVec4(73, 77, 69, 95)), MakeVec4(77, 69, 84, 65)), MakeVec4(68, 65, 84, 65)), MakeVec4(95, 75, 69, 89));
    assume $IsValid'vec'u8''($t34);

    // $t35 := string::utf8($t34) on_abort goto L13 with $t21 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:378:79+34
    call $t35 := $1_string_utf8($t34);
    if ($abort_flag) {
        assume {:print "$at(153,20322,20356)"} true;
        $t21 := $abort_code;
        assume {:print "$track_abort(30,11):", $t21} $t21 == $t21;
        goto L13;
    }

    // $t36 := simple_map::borrow<string::String, vector<u8>>($t33, $t35) on_abort goto L13 with $t21 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:378:39+75
    call $t36 := $1_simple_map_borrow'$1_string_String_vec'u8''($t33, $t35);
    if ($abort_flag) {
        assume {:print "$at(153,20282,20357)"} true;
        $t21 := $abort_code;
        assume {:print "$track_abort(30,11):", $t21} $t21 == $t21;
        goto L13;
    }

    // $t37 := from_bcs::to_u64($t36) on_abort goto L13 with $t21 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:378:31+84
    call $t37 := $1_from_bcs_to_u64($t36);
    if ($abort_flag) {
        assume {:print "$at(153,20274,20358)"} true;
        $t21 := $abort_code;
        assume {:print "$track_abort(30,11):", $t21} $t21 == $t21;
        goto L13;
    }

    // trace_local[resolvable_time]($t37) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:378:13+15
    assume {:print "$track_local(30,11,5):", $t37} $t37 == $t37;

    // $t38 := timestamp::now_seconds() on_abort goto L13 with $t21 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:379:17+24
    assume {:print "$at(153,20376,20400)"} true;
    call $t38 := $1_timestamp_now_seconds();
    if ($abort_flag) {
        assume {:print "$at(153,20376,20400)"} true;
        $t21 := $abort_code;
        assume {:print "$track_abort(30,11):", $t21} $t21 == $t21;
        goto L13;
    }

    // $t39 := >($t38, $t37) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:379:42+1
    call $t39 := $Gt($t38, $t37);

    // if ($t39) goto L7 else goto L6 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:379:9+103
    if ($t39) { goto L7; } else { goto L6; }

    // label L7 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:379:9+103
L7:

    // goto L8 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:379:9+103
    assume {:print "$at(153,20368,20471)"} true;
    goto L8;

    // label L6 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:379:9+103
L6:

    // pack_ref_deep($t26) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:379:9+103
    assume {:print "$at(153,20368,20471)"} true;

    // destroy($t28) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:379:9+103

    // $t40 := 8 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:379:82+28
    $t40 := 8;
    assume $IsValid'u64'($t40);

    // $t41 := error::invalid_state($t40) on_abort goto L13 with $t21 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:379:61+50
    call $t41 := $1_error_invalid_state($t40);
    if ($abort_flag) {
        assume {:print "$at(153,20420,20470)"} true;
        $t21 := $abort_code;
        assume {:print "$track_abort(30,11):", $t21} $t21 == $t21;
        goto L13;
    }

    // trace_abort($t41) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:379:9+103
    assume {:print "$at(153,20368,20471)"} true;
    assume {:print "$track_abort(30,11):", $t41} $t41 == $t41;

    // $t21 := move($t41) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:379:9+103
    $t21 := $t41;

    // goto L13 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:379:9+103
    goto L13;

    // label L8 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:382:13+38
    assume {:print "$at(153,20503,20541)"} true;
L8:

    // $t42 := opaque begin: transaction_context::get_script_hash() at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:382:13+38
    assume {:print "$at(153,20503,20541)"} true;

    // assume WellFormed($t42) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:382:13+38
    assume $IsValid'vec'u8''($t42);

    // assume Eq<vector<u8>>($t42, transaction_context::spec_get_script_hash()) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:382:13+38
    assume $IsEqual'vec'u8''($t42, $1_transaction_context_spec_get_script_hash());

    // $t42 := opaque end: transaction_context::get_script_hash() at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:382:13+38

    // $t43 := get_field<voting::Proposal<#0>>.execution_hash($t28) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:382:55+23
    $t43 := $execution_hash#$1_voting_Proposal'$1_governance_proposal_GovernanceProposal'($Dereference($t28));

    // pack_ref_deep($t26) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:382:55+23

    // $t44 := ==($t42, $t43) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:382:52+2
    $t44 := $IsEqual'vec'u8''($t42, $t43);

    // if ($t44) goto L10 else goto L9 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:381:9+173
    assume {:print "$at(153,20482,20655)"} true;
    if ($t44) { goto L10; } else { goto L9; }

    // label L10 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:381:9+173
L10:

    // goto L11 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:381:9+173
    assume {:print "$at(153,20482,20655)"} true;
    goto L11;

    // label L9 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:383:37+37
    assume {:print "$at(153,20606,20643)"} true;
L9:

    // $t45 := 1 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:383:37+37
    assume {:print "$at(153,20606,20643)"} true;
    $t45 := 1;
    assume $IsValid'u64'($t45);

    // $t46 := error::invalid_argument($t45) on_abort goto L13 with $t21 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:383:13+62
    call $t46 := $1_error_invalid_argument($t45);
    if ($abort_flag) {
        assume {:print "$at(153,20582,20644)"} true;
        $t21 := $abort_code;
        assume {:print "$track_abort(30,11):", $t21} $t21 == $t21;
        goto L13;
    }

    // trace_abort($t46) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:381:9+173
    assume {:print "$at(153,20482,20655)"} true;
    assume {:print "$track_abort(30,11):", $t46} $t46 == $t46;

    // $t21 := move($t46) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:381:9+173
    $t21 := $t46;

    // goto L13 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:381:9+173
    goto L13;

    // label L11 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:384:10+1
    assume {:print "$at(153,20655,20656)"} true;
L11:

    // label L12 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:385:5+1
    assume {:print "$at(153,20661,20662)"} true;
L12:

    // return () at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:385:5+1
    assume {:print "$at(153,20661,20662)"} true;
    return;

    // label L13 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:385:5+1
L13:

    // abort($t21) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:385:5+1
    assume {:print "$at(153,20661,20662)"} true;
    $abort_code := $t21;
    $abort_flag := true;
    return;

}

// fun voting::is_resolved<governance_proposal::GovernanceProposal> [baseline] at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:611:5+346
procedure {:inline 1} $1_voting_is_resolved'$1_governance_proposal_GovernanceProposal'(_$t0: int, _$t1: int) returns ($ret0: bool)
{
    // declare local variables
    var $t2: $1_voting_VotingForum'$1_governance_proposal_GovernanceProposal';
    var $t3: $1_voting_VotingForum'$1_governance_proposal_GovernanceProposal';
    var $t4: int;
    var $t5: Table int ($1_voting_Proposal'$1_governance_proposal_GovernanceProposal');
    var $t6: $1_voting_Proposal'$1_governance_proposal_GovernanceProposal';
    var $t7: bool;
    var $t0: int;
    var $t1: int;
    var $temp_0'address': int;
    var $temp_0'bool': bool;
    var $temp_0'u64': int;
    $t0 := _$t0;
    $t1 := _$t1;

    // bytecode translation starts here
    // assume Identical($t2, global<voting::VotingForum<#0>>($t0)) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.spec.move:286:9+75
    assume {:print "$at(154,12822,12897)"} true;
    assume ($t2 == $ResourceValue($1_voting_VotingForum'$1_governance_proposal_GovernanceProposal'_$memory, $t0));

    // trace_local[voting_forum_address]($t0) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:611:5+1
    assume {:print "$at(153,31484,31485)"} true;
    assume {:print "$track_local(30,12,0):", $t0} $t0 == $t0;

    // trace_local[proposal_id]($t1) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:611:5+1
    assume {:print "$track_local(30,12,1):", $t1} $t1 == $t1;

    // $t3 := get_global<voting::VotingForum<#0>>($t0) on_abort goto L2 with $t4 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:615:28+13
    assume {:print "$at(153,31656,31669)"} true;
    if (!$ResourceExists($1_voting_VotingForum'$1_governance_proposal_GovernanceProposal'_$memory, $t0)) {
        call $ExecFailureAbort();
    } else {
        $t3 := $ResourceValue($1_voting_VotingForum'$1_governance_proposal_GovernanceProposal'_$memory, $t0);
    }
    if ($abort_flag) {
        assume {:print "$at(153,31656,31669)"} true;
        $t4 := $abort_code;
        assume {:print "$track_abort(30,12):", $t4} $t4 == $t4;
        goto L2;
    }

    // $t5 := get_field<voting::VotingForum<#0>>.proposals($t3) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:616:38+23
    assume {:print "$at(153,31757,31780)"} true;
    $t5 := $proposals#$1_voting_VotingForum'$1_governance_proposal_GovernanceProposal'($t3);

    // $t6 := table::borrow<u64, voting::Proposal<#0>>($t5, $t1) on_abort goto L2 with $t4 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:616:24+51
    call $t6 := $1_table_borrow'u64_$1_voting_Proposal'$1_governance_proposal_GovernanceProposal''($t5, $t1);
    if ($abort_flag) {
        assume {:print "$at(153,31743,31794)"} true;
        $t4 := $abort_code;
        assume {:print "$track_abort(30,12):", $t4} $t4 == $t4;
        goto L2;
    }

    // $t7 := get_field<voting::Proposal<#0>>.is_resolved($t6) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:617:9+20
    assume {:print "$at(153,31804,31824)"} true;
    $t7 := $is_resolved#$1_voting_Proposal'$1_governance_proposal_GovernanceProposal'($t6);

    // trace_return[0]($t7) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:617:9+20
    assume {:print "$track_return(30,12,0):", $t7} $t7 == $t7;

    // label L1 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:618:5+1
    assume {:print "$at(153,31829,31830)"} true;
L1:

    // return $t7 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:618:5+1
    assume {:print "$at(153,31829,31830)"} true;
    $ret0 := $t7;
    return;

    // label L2 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:618:5+1
L2:

    // abort($t4) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:618:5+1
    assume {:print "$at(153,31829,31830)"} true;
    $abort_code := $t4;
    $abort_flag := true;
    return;

}

// fun voting::is_voting_closed<governance_proposal::GovernanceProposal> [baseline] at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:500:5+374
procedure {:inline 1} $1_voting_is_voting_closed'$1_governance_proposal_GovernanceProposal'(_$t0: int, _$t1: int) returns ($ret0: bool)
{
    // declare local variables
    var $t2: bool;
    var $t3: $1_voting_Proposal'$1_governance_proposal_GovernanceProposal';
    var $t4: $1_voting_VotingForum'$1_governance_proposal_GovernanceProposal';
    var $t5: $1_voting_VotingForum'$1_governance_proposal_GovernanceProposal';
    var $t6: int;
    var $t7: Table int ($1_voting_Proposal'$1_governance_proposal_GovernanceProposal');
    var $t8: $1_voting_Proposal'$1_governance_proposal_GovernanceProposal';
    var $t9: bool;
    var $t10: bool;
    var $t0: int;
    var $t1: int;
    var $temp_0'$1_voting_Proposal'$1_governance_proposal_GovernanceProposal'': $1_voting_Proposal'$1_governance_proposal_GovernanceProposal';
    var $temp_0'address': int;
    var $temp_0'bool': bool;
    var $temp_0'u64': int;
    $t0 := _$t0;
    $t1 := _$t1;

    // bytecode translation starts here
    // assume Identical($t4, global<voting::VotingForum<#0>>($t0)) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.spec.move:286:9+75
    assume {:print "$at(154,12822,12897)"} true;
    assume ($t4 == $ResourceValue($1_voting_VotingForum'$1_governance_proposal_GovernanceProposal'_$memory, $t0));

    // assume chain_status::$is_operating() at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.spec.move:177:9+38
    assume {:print "$at(154,8721,8759)"} true;
    assume $1_chain_status_$is_operating($1_chain_status_GenesisEndMarker_$memory);

    // trace_local[voting_forum_address]($t0) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:500:5+1
    assume {:print "$at(153,26722,26723)"} true;
    assume {:print "$track_local(30,13,0):", $t0} $t0 == $t0;

    // trace_local[proposal_id]($t1) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:500:5+1
    assume {:print "$track_local(30,13,1):", $t1} $t1 == $t1;

    // $t5 := get_global<voting::VotingForum<#0>>($t0) on_abort goto L4 with $t6 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:501:28+13
    assume {:print "$at(153,26876,26889)"} true;
    if (!$ResourceExists($1_voting_VotingForum'$1_governance_proposal_GovernanceProposal'_$memory, $t0)) {
        call $ExecFailureAbort();
    } else {
        $t5 := $ResourceValue($1_voting_VotingForum'$1_governance_proposal_GovernanceProposal'_$memory, $t0);
    }
    if ($abort_flag) {
        assume {:print "$at(153,26876,26889)"} true;
        $t6 := $abort_code;
        assume {:print "$track_abort(30,13):", $t6} $t6 == $t6;
        goto L4;
    }

    // $t7 := get_field<voting::VotingForum<#0>>.proposals($t5) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:502:38+23
    assume {:print "$at(153,26977,27000)"} true;
    $t7 := $proposals#$1_voting_VotingForum'$1_governance_proposal_GovernanceProposal'($t5);

    // $t8 := table::borrow<u64, voting::Proposal<#0>>($t7, $t1) on_abort goto L4 with $t6 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:502:24+51
    call $t8 := $1_table_borrow'u64_$1_voting_Proposal'$1_governance_proposal_GovernanceProposal''($t7, $t1);
    if ($abort_flag) {
        assume {:print "$at(153,26963,27014)"} true;
        $t6 := $abort_code;
        assume {:print "$track_abort(30,13):", $t6} $t6 == $t6;
        goto L4;
    }

    // trace_local[proposal]($t8) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:502:13+8
    assume {:print "$track_local(30,13,3):", $t8} $t8 == $t8;

    // $t9 := voting::can_be_resolved_early<#0>($t8) on_abort goto L4 with $t6 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:503:9+31
    assume {:print "$at(153,27024,27055)"} true;
    call $t9 := $1_voting_can_be_resolved_early'$1_governance_proposal_GovernanceProposal'($t8);
    if ($abort_flag) {
        assume {:print "$at(153,27024,27055)"} true;
        $t6 := $abort_code;
        assume {:print "$track_abort(30,13):", $t6} $t6 == $t6;
        goto L4;
    }

    // if ($t9) goto L1 else goto L0 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:503:9+66
    if ($t9) { goto L1; } else { goto L0; }

    // label L1 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:503:9+66
L1:

    // $t10 := true at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:503:9+66
    assume {:print "$at(153,27024,27090)"} true;
    $t10 := true;
    assume $IsValid'bool'($t10);

    // $t2 := $t10 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:503:9+66
    $t2 := $t10;

    // goto L2 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:503:9+66
    goto L2;

    // label L0 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:503:66+8
L0:

    // $t2 := voting::is_voting_period_over<#0>($t8) on_abort goto L4 with $t6 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:503:44+31
    assume {:print "$at(153,27059,27090)"} true;
    call $t2 := $1_voting_is_voting_period_over'$1_governance_proposal_GovernanceProposal'($t8);
    if ($abort_flag) {
        assume {:print "$at(153,27059,27090)"} true;
        $t6 := $abort_code;
        assume {:print "$track_abort(30,13):", $t6} $t6 == $t6;
        goto L4;
    }

    // label L2 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:503:9+66
L2:

    // trace_return[0]($t2) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:503:9+66
    assume {:print "$at(153,27024,27090)"} true;
    assume {:print "$track_return(30,13,0):", $t2} $t2 == $t2;

    // label L3 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:504:5+1
    assume {:print "$at(153,27095,27096)"} true;
L3:

    // return $t2 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:504:5+1
    assume {:print "$at(153,27095,27096)"} true;
    $ret0 := $t2;
    return;

    // label L4 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:504:5+1
L4:

    // abort($t6) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:504:5+1
    assume {:print "$at(153,27095,27096)"} true;
    $abort_code := $t6;
    $abort_flag := true;
    return;

}

// fun voting::is_voting_period_over<governance_proposal::GovernanceProposal> [baseline] at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:634:5+155
procedure {:inline 1} $1_voting_is_voting_period_over'$1_governance_proposal_GovernanceProposal'(_$t0: $1_voting_Proposal'$1_governance_proposal_GovernanceProposal') returns ($ret0: bool)
{
    // declare local variables
    var $t1: int;
    var $t2: int;
    var $t3: int;
    var $t4: bool;
    var $t0: $1_voting_Proposal'$1_governance_proposal_GovernanceProposal';
    var $temp_0'$1_voting_Proposal'$1_governance_proposal_GovernanceProposal'': $1_voting_Proposal'$1_governance_proposal_GovernanceProposal';
    var $temp_0'bool': bool;
    $t0 := _$t0;

    // bytecode translation starts here
    // assume chain_status::$is_operating() at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.spec.move:310:9+38
    assume {:print "$at(154,14142,14180)"} true;
    assume $1_chain_status_$is_operating($1_chain_status_GenesisEndMarker_$memory);

    // trace_local[proposal]($t0) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:634:5+1
    assume {:print "$at(153,32691,32692)"} true;
    assume {:print "$track_local(30,14,0):", $t0} $t0 == $t0;

    // $t1 := timestamp::now_seconds() on_abort goto L2 with $t2 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:635:9+24
    assume {:print "$at(153,32789,32813)"} true;
    call $t1 := $1_timestamp_now_seconds();
    if ($abort_flag) {
        assume {:print "$at(153,32789,32813)"} true;
        $t2 := $abort_code;
        assume {:print "$track_abort(30,14):", $t2} $t2 == $t2;
        goto L2;
    }

    // $t3 := get_field<voting::Proposal<#0>>.expiration_secs($t0) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:635:36+24
    $t3 := $expiration_secs#$1_voting_Proposal'$1_governance_proposal_GovernanceProposal'($t0);

    // $t4 := >($t1, $t3) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:635:34+1
    call $t4 := $Gt($t1, $t3);

    // trace_return[0]($t4) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:635:9+51
    assume {:print "$track_return(30,14,0):", $t4} $t4 == $t4;

    // label L1 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:636:5+1
    assume {:print "$at(153,32845,32846)"} true;
L1:

    // return $t4 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:636:5+1
    assume {:print "$at(153,32845,32846)"} true;
    $ret0 := $t4;
    return;

    // label L2 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:636:5+1
L2:

    // abort($t2) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:636:5+1
    assume {:print "$at(153,32845,32846)"} true;
    $abort_code := $t2;
    $abort_flag := true;
    return;

}

// fun voting::resolve_proposal_v2<governance_proposal::GovernanceProposal> [baseline] at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:434:5+3354
procedure {:inline 1} $1_voting_resolve_proposal_v2'$1_governance_proposal_GovernanceProposal'(_$t0: int, _$t1: int, _$t2: Vec (int)) returns ()
{
    // declare local variables
    var $t3: bool;
    var $t4: bool;
    var $t5: bool;
    var $t6: bool;
    var $t7: $Mutation (Vec (int));
    var $t8: $Mutation (Vec (int));
    var $t9: $1_string_String;
    var $t10: $1_string_String;
    var $t11: bool;
    var $t12: $Mutation ($1_voting_Proposal'$1_governance_proposal_GovernanceProposal');
    var $t13: bool;
    var $t14: $Mutation ($1_voting_VotingForum'$1_governance_proposal_GovernanceProposal');
    var $t15: $1_voting_VotingForum'$1_governance_proposal_GovernanceProposal';
    var $t16: $1_voting_VotingForum'$1_governance_proposal_GovernanceProposal';
    var $t17: $1_voting_Proposal'$1_governance_proposal_GovernanceProposal';
    var $t18: int;
    var $t19: bool;
    var $t20: bool;
    var $t21: bool;
    var $t22: $1_voting_VotingForum'$1_governance_proposal_GovernanceProposal';
    var $t23: int;
    var $t24: $Mutation ($1_voting_VotingForum'$1_governance_proposal_GovernanceProposal');
    var $t25: $Mutation (Table int ($1_voting_Proposal'$1_governance_proposal_GovernanceProposal'));
    var $t26: $Mutation ($1_voting_Proposal'$1_governance_proposal_GovernanceProposal');
    var $t27: Vec (int);
    var $t28: $1_string_String;
    var $t29: Table int (Vec (int));
    var $t30: bool;
    var $t31: $Mutation (Table int (Vec (int)));
    var $t32: $Mutation (Vec (int));
    var $t33: bool;
    var $t34: Vec (int);
    var $t35: Vec (int);
    var $t36: $1_string_String;
    var $t37: Table int (Vec (int));
    var $t38: bool;
    var $t39: Table int (Vec (int));
    var $t40: Vec (int);
    var $t41: bool;
    var $t42: int;
    var $t43: int;
    var $t44: bool;
    var $t45: bool;
    var $t46: int;
    var $t47: int;
    var $t48: bool;
    var $t49: $Mutation (bool);
    var $t50: int;
    var $t51: $Mutation (int);
    var $t52: $Mutation (Table int (Vec (int)));
    var $t53: $Mutation (Vec (int));
    var $t54: bool;
    var $t55: Vec (int);
    var $t56: $Mutation (Vec (int));
    var $t57: $1_voting_Proposal'$1_governance_proposal_GovernanceProposal';
    var $t58: bool;
    var $t59: $Mutation ($1_voting_VotingEvents);
    var $t60: $Mutation ($1_event_EventHandle'$1_voting_ResolveProposal');
    var $t61: int;
    var $t62: int;
    var $t63: $1_voting_ResolveProposal;
    var $t0: int;
    var $t1: int;
    var $t2: Vec (int);
    var $temp_0'$1_string_String': $1_string_String;
    var $temp_0'$1_voting_Proposal'$1_governance_proposal_GovernanceProposal'': $1_voting_Proposal'$1_governance_proposal_GovernanceProposal';
    var $temp_0'$1_voting_VotingForum'$1_governance_proposal_GovernanceProposal'': $1_voting_VotingForum'$1_governance_proposal_GovernanceProposal';
    var $temp_0'address': int;
    var $temp_0'bool': bool;
    var $temp_0'u64': int;
    var $temp_0'vec'u8'': Vec (int);
    $t0 := _$t0;
    $t1 := _$t1;
    $t2 := _$t2;

    // bytecode translation starts here
    // assume Identical($t15, global<voting::VotingForum<#0>>($t0)) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.spec.move:286:9+75
    assume {:print "$at(154,12822,12897)"} true;
    assume ($t15 == $ResourceValue($1_voting_VotingForum'$1_governance_proposal_GovernanceProposal'_$memory, $t0));

    // assume chain_status::$is_operating() at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.spec.move:163:9+38
    assume {:print "$at(154,8035,8073)"} true;
    assume $1_chain_status_$is_operating($1_chain_status_GenesisEndMarker_$memory);

    // trace_local[voting_forum_address]($t0) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:434:5+1
    assume {:print "$at(153,23042,23043)"} true;
    assume {:print "$track_local(30,18,0):", $t0} $t0 == $t0;

    // trace_local[proposal_id]($t1) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:434:5+1
    assume {:print "$track_local(30,18,1):", $t1} $t1 == $t1;

    // trace_local[next_execution_hash]($t2) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:434:5+1
    assume {:print "$track_local(30,18,2):", $t2} $t2 == $t2;

    // assume Identical($t16, global<voting::VotingForum<#0>>($t0)) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.spec.move:124:9+75
    assume {:print "$at(154,5795,5870)"} true;
    assume ($t16 == $ResourceValue($1_voting_VotingForum'$1_governance_proposal_GovernanceProposal'_$memory, $t0));

    // assume Identical($t17, table::spec_get<u64, voting::Proposal<#0>>(select voting::VotingForum.proposals($t16), $t1)) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.spec.move:125:9+68
    assume {:print "$at(154,5879,5947)"} true;
    assume ($t17 == $1_table_spec_get'u64_$1_voting_Proposal'$1_governance_proposal_GovernanceProposal''($proposals#$1_voting_VotingForum'$1_governance_proposal_GovernanceProposal'($t16), $t1));

    // assume Identical($t18, option::spec_borrow<u128>(select voting::Proposal.early_resolution_vote_threshold($t17))) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.spec.move:126:9+95
    assume {:print "$at(154,5956,6051)"} true;
    assume ($t18 == $1_option_spec_borrow'u128'($early_resolution_vote_threshold#$1_voting_Proposal'$1_governance_proposal_GovernanceProposal'($t17)));

    // assume Identical($t19, Gt(timestamp::$now_seconds(), select voting::Proposal.expiration_secs($t17))) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.spec.move:127:9+77
    assume {:print "$at(154,6060,6137)"} true;
    assume ($t19 == ($1_timestamp_$now_seconds($1_timestamp_CurrentTimeMicroseconds_$memory) > $expiration_secs#$1_voting_Proposal'$1_governance_proposal_GovernanceProposal'($t17)));

    // assume Identical($t20, And(option::spec_is_some<u128>(select voting::Proposal.early_resolution_vote_threshold($t17)), Or(Ge(select voting::Proposal.yes_votes($t17), $t18), Ge(select voting::Proposal.no_votes($t17), $t18)))) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.spec.move:128:9+266
    assume {:print "$at(154,6146,6412)"} true;
    assume ($t20 == ($1_option_spec_is_some'u128'($early_resolution_vote_threshold#$1_voting_Proposal'$1_governance_proposal_GovernanceProposal'($t17)) && (($yes_votes#$1_voting_Proposal'$1_governance_proposal_GovernanceProposal'($t17) >= $t18) || ($no_votes#$1_voting_Proposal'$1_governance_proposal_GovernanceProposal'($t17) >= $t18))));

    // assume Identical($t21, Or($t19, $t20)) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.spec.move:131:9+60
    assume {:print "$at(154,6421,6481)"} true;
    assume ($t21 == ($t19 || $t20));

    // assume Identical($t22, global<voting::VotingForum<#0>>($t0)) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.spec.move:286:9+75
    assume {:print "$at(154,12822,12897)"} true;
    assume ($t22 == $ResourceValue($1_voting_VotingForum'$1_governance_proposal_GovernanceProposal'_$memory, $t0));

    // voting::is_proposal_resolvable<#0>($t0, $t1) on_abort goto L14 with $t23 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:439:9+71
    assume {:print "$at(153,23238,23309)"} true;
    call $1_voting_is_proposal_resolvable'$1_governance_proposal_GovernanceProposal'($t0, $t1);
    if ($abort_flag) {
        assume {:print "$at(153,23238,23309)"} true;
        $t23 := $abort_code;
        assume {:print "$track_abort(30,18):", $t23} $t23 == $t23;
        goto L14;
    }

    // $t24 := borrow_global<voting::VotingForum<#0>>($t0) on_abort goto L14 with $t23 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:441:28+17
    assume {:print "$at(153,23339,23356)"} true;
    if (!$ResourceExists($1_voting_VotingForum'$1_governance_proposal_GovernanceProposal'_$memory, $t0)) {
        call $ExecFailureAbort();
    } else {
        $t24 := $Mutation($Global($t0), EmptyVec(), $ResourceValue($1_voting_VotingForum'$1_governance_proposal_GovernanceProposal'_$memory, $t0));
    }
    if ($abort_flag) {
        assume {:print "$at(153,23339,23356)"} true;
        $t23 := $abort_code;
        assume {:print "$track_abort(30,18):", $t23} $t23 == $t23;
        goto L14;
    }

    // trace_local[voting_forum]($t24) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:441:13+12
    $temp_0'$1_voting_VotingForum'$1_governance_proposal_GovernanceProposal'' := $Dereference($t24);
    assume {:print "$track_local(30,18,14):", $temp_0'$1_voting_VotingForum'$1_governance_proposal_GovernanceProposal''} $temp_0'$1_voting_VotingForum'$1_governance_proposal_GovernanceProposal'' == $temp_0'$1_voting_VotingForum'$1_governance_proposal_GovernanceProposal'';

    // $t25 := borrow_field<voting::VotingForum<#0>>.proposals($t24) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:442:42+27
    assume {:print "$at(153,23448,23475)"} true;
    $t25 := $ChildMutation($t24, 0, $proposals#$1_voting_VotingForum'$1_governance_proposal_GovernanceProposal'($Dereference($t24)));

    // $t26 := table::borrow_mut<u64, voting::Proposal<#0>>($t25, $t1) on_abort goto L14 with $t23 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:442:24+59
    call $t26,$t25 := $1_table_borrow_mut'u64_$1_voting_Proposal'$1_governance_proposal_GovernanceProposal''($t25, $t1);
    if ($abort_flag) {
        assume {:print "$at(153,23430,23489)"} true;
        $t23 := $abort_code;
        assume {:print "$track_abort(30,18):", $t23} $t23 == $t23;
        goto L14;
    }

    // trace_local[proposal]($t26) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:442:13+8
    $temp_0'$1_voting_Proposal'$1_governance_proposal_GovernanceProposal'' := $Dereference($t26);
    assume {:print "$track_local(30,18,12):", $temp_0'$1_voting_Proposal'$1_governance_proposal_GovernanceProposal''} $temp_0'$1_voting_Proposal'$1_governance_proposal_GovernanceProposal'' == $temp_0'$1_voting_Proposal'$1_governance_proposal_GovernanceProposal'';

    // $t27 := [73, 83, 95, 77, 85, 76, 84, 73, 95, 83, 84, 69, 80, 95, 80, 82, 79, 80, 79, 83, 65, 76, 95, 73, 78, 95, 69, 88, 69, 67, 85, 84, 73, 79, 78] at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:445:48+39
    assume {:print "$at(153,23663,23702)"} true;
    $t27 := ConcatVec(ConcatVec(ConcatVec(ConcatVec(ConcatVec(ConcatVec(ConcatVec(ConcatVec(MakeVec4(73, 83, 95, 77), MakeVec4(85, 76, 84, 73)), MakeVec4(95, 83, 84, 69)), MakeVec4(80, 95, 80, 82)), MakeVec4(79, 80, 79, 83)), MakeVec4(65, 76, 95, 73)), MakeVec4(78, 95, 69, 88)), MakeVec4(69, 67, 85, 84)), MakeVec3(73, 79, 78));
    assume $IsValid'vec'u8''($t27);

    // $t28 := string::utf8($t27) on_abort goto L14 with $t23 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:445:43+45
    call $t28 := $1_string_utf8($t27);
    if ($abort_flag) {
        assume {:print "$at(153,23658,23703)"} true;
        $t23 := $abort_code;
        assume {:print "$track_abort(30,18):", $t23} $t23 == $t23;
        goto L14;
    }

    // trace_local[multi_step_in_execution_key]($t28) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:445:13+27
    assume {:print "$track_local(30,18,9):", $t28} $t28 == $t28;

    // $t29 := get_field<voting::Proposal<#0>>.metadata($t26) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:446:38+18
    assume {:print "$at(153,23742,23760)"} true;
    $t29 := $metadata#$1_voting_Proposal'$1_governance_proposal_GovernanceProposal'($Dereference($t26));

    // $t30 := simple_map::contains_key<string::String, vector<u8>>($t29, $t28) on_abort goto L14 with $t23 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:446:13+74
    call $t30 := $1_simple_map_contains_key'$1_string_String_vec'u8''($t29, $t28);
    if ($abort_flag) {
        assume {:print "$at(153,23717,23791)"} true;
        $t23 := $abort_code;
        assume {:print "$track_abort(30,18):", $t23} $t23 == $t23;
        goto L14;
    }

    // if ($t30) goto L1 else goto L0 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:446:9+303
    if ($t30) { goto L1; } else { goto L0; }

    // label L1 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:447:89+8
    assume {:print "$at(153,23883,23891)"} true;
L1:

    // $t31 := borrow_field<voting::Proposal<#0>>.metadata($t26) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:447:84+22
    assume {:print "$at(153,23878,23900)"} true;
    $t31 := $ChildMutation($t26, 2, $metadata#$1_voting_Proposal'$1_governance_proposal_GovernanceProposal'($Dereference($t26)));

    // $t32 := simple_map::borrow_mut<string::String, vector<u8>>($t31, $t28) on_abort goto L14 with $t23 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:447:61+76
    call $t32,$t31 := $1_simple_map_borrow_mut'$1_string_String_vec'u8''($t31, $t28);
    if ($abort_flag) {
        assume {:print "$at(153,23855,23931)"} true;
        $t23 := $abort_code;
        assume {:print "$track_abort(30,18):", $t23} $t23 == $t23;
        goto L14;
    }

    // trace_local[is_multi_step_proposal_in_execution_value]($t32) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:447:17+41
    $temp_0'vec'u8'' := $Dereference($t32);
    assume {:print "$track_local(30,18,7):", $temp_0'vec'u8''} $temp_0'vec'u8'' == $temp_0'vec'u8'';

    // $t33 := true at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:448:68+4
    assume {:print "$at(153,24000,24004)"} true;
    $t33 := true;
    assume $IsValid'bool'($t33);

    // $t34 := bcs::to_bytes<bool>($t33) on_abort goto L14 with $t23 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:448:58+15
    call $t34 := $1_bcs_to_bytes'bool'($t33);
    if ($abort_flag) {
        assume {:print "$at(153,23990,24005)"} true;
        $t23 := $abort_code;
        assume {:print "$track_abort(30,18):", $t23} $t23 == $t23;
        goto L14;
    }

    // write_ref($t32, $t34) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:448:13+60
    $t32 := $UpdateMutation($t32, $t34);

    // write_back[Reference($t31)[]]($t32) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:448:13+60
    $t31 := $UpdateMutation($t31, UpdateTable($Dereference($t31), ReadVec(p#$Mutation($t32), LenVec(p#$Mutation($t31))), $Dereference($t32)));

    // write_back[Reference($t26).metadata (simple_map::SimpleMap<string::String, vector<u8>>)]($t31) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:448:13+60
    $t26 := $UpdateMutation($t26, $Update'$1_voting_Proposal'$1_governance_proposal_GovernanceProposal''_metadata($Dereference($t26), $Dereference($t31)));

    // label L0 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:451:35+26
    assume {:print "$at(153,24053,24079)"} true;
L0:

    // $t35 := [73, 83, 95, 77, 85, 76, 84, 73, 95, 83, 84, 69, 80, 95, 80, 82, 79, 80, 79, 83, 65, 76, 95, 75, 69, 89] at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:451:35+26
    assume {:print "$at(153,24053,24079)"} true;
    $t35 := ConcatVec(ConcatVec(ConcatVec(ConcatVec(ConcatVec(ConcatVec(MakeVec4(73, 83, 95, 77), MakeVec4(85, 76, 84, 73)), MakeVec4(95, 83, 84, 69)), MakeVec4(80, 95, 80, 82)), MakeVec4(79, 80, 79, 83)), MakeVec4(65, 76, 95, 75)), MakeVec2(69, 89));
    assume $IsValid'vec'u8''($t35);

    // $t36 := string::utf8($t35) on_abort goto L14 with $t23 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:451:30+32
    call $t36 := $1_string_utf8($t35);
    if ($abort_flag) {
        assume {:print "$at(153,24048,24080)"} true;
        $t23 := $abort_code;
        assume {:print "$track_abort(30,18):", $t23} $t23 == $t23;
        goto L14;
    }

    // trace_local[multi_step_key]($t36) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:451:13+14
    assume {:print "$track_local(30,18,10):", $t36} $t36 == $t36;

    // $t37 := get_field<voting::Proposal<#0>>.metadata($t26) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:452:54+18
    assume {:print "$at(153,24135,24153)"} true;
    $t37 := $metadata#$1_voting_Proposal'$1_governance_proposal_GovernanceProposal'($Dereference($t26));

    // $t38 := simple_map::contains_key<string::String, vector<u8>>($t37, $t36) on_abort goto L14 with $t23 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:452:29+61
    call $t38 := $1_simple_map_contains_key'$1_string_String_vec'u8''($t37, $t36);
    if ($abort_flag) {
        assume {:print "$at(153,24110,24171)"} true;
        $t23 := $abort_code;
        assume {:print "$track_abort(30,18):", $t23} $t23 == $t23;
        goto L14;
    }

    // if ($t38) goto L3 else goto L2 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:452:29+140
    if ($t38) { goto L3; } else { goto L2; }

    // label L3 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:452:133+8
L3:

    // $t39 := get_field<voting::Proposal<#0>>.metadata($t26) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:452:132+18
    assume {:print "$at(153,24213,24231)"} true;
    $t39 := $metadata#$1_voting_Proposal'$1_governance_proposal_GovernanceProposal'($Dereference($t26));

    // $t40 := simple_map::borrow<string::String, vector<u8>>($t39, $t36) on_abort goto L14 with $t23 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:452:113+55
    call $t40 := $1_simple_map_borrow'$1_string_String_vec'u8''($t39, $t36);
    if ($abort_flag) {
        assume {:print "$at(153,24194,24249)"} true;
        $t23 := $abort_code;
        assume {:print "$track_abort(30,18):", $t23} $t23 == $t23;
        goto L14;
    }

    // $t4 := from_bcs::to_bool($t40) on_abort goto L14 with $t23 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:452:94+75
    call $t4 := $1_from_bcs_to_bool($t40);
    if ($abort_flag) {
        assume {:print "$at(153,24175,24250)"} true;
        $t23 := $abort_code;
        assume {:print "$track_abort(30,18):", $t23} $t23 == $t23;
        goto L14;
    }

    // goto L4 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:452:29+140
    goto L4;

    // label L2 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:452:29+140
L2:

    // $t41 := false at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:452:29+140
    assume {:print "$at(153,24110,24250)"} true;
    $t41 := false;
    assume $IsValid'bool'($t41);

    // $t4 := $t41 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:452:29+140
    $t4 := $t41;

    // label L4 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:452:29+140
L4:

    // trace_local[is_multi_step]($t4) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:452:13+13
    assume {:print "$at(153,24094,24107)"} true;
    assume {:print "$track_local(30,18,6):", $t4} $t4 == $t4;

    // $t42 := vector::length<u8>($t2) on_abort goto L14 with $t23 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:453:44+36
    assume {:print "$at(153,24295,24331)"} true;
    call $t42 := $1_vector_length'u8'($t2);
    if ($abort_flag) {
        assume {:print "$at(153,24295,24331)"} true;
        $t23 := $abort_code;
        assume {:print "$track_abort(30,18):", $t23} $t23 == $t23;
        goto L14;
    }

    // $t43 := 0 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:453:84+1
    $t43 := 0;
    assume $IsValid'u64'($t43);

    // $t44 := ==($t42, $t43) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:453:81+2
    $t44 := $IsEqual'u64'($t42, $t43);

    // trace_local[next_execution_hash_is_empty]($t44) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:453:13+28
    assume {:print "$track_local(30,18,11):", $t44} $t44 == $t44;

    // $t45 := ||($t4, $t44) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:456:31+2
    assume {:print "$at(153,24471,24473)"} true;
    call $t45 := $Or($t4, $t44);

    // if ($t45) goto L6 else goto L5 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:456:9+134
    if ($t45) { goto L6; } else { goto L5; }

    // label L6 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:456:9+134
L6:

    // goto L7 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:456:9+134
    assume {:print "$at(153,24449,24583)"} true;
    goto L7;

    // label L5 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:456:9+134
L5:

    // destroy($t24) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:456:9+134
    assume {:print "$at(153,24449,24583)"} true;

    // write_back[Reference($t25)[]]($t26) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:456:9+134
    $t25 := $UpdateMutation($t25, UpdateTable($Dereference($t25), ReadVec(p#$Mutation($t26), LenVec(p#$Mutation($t25))), $Dereference($t26)));

    // write_back[Reference($t24).proposals (table::Table<u64, voting::Proposal<#0>>)]($t25) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:456:9+134
    $t24 := $UpdateMutation($t24, $Update'$1_voting_VotingForum'$1_governance_proposal_GovernanceProposal''_proposals($Dereference($t24), $Dereference($t25)));

    // pack_ref_deep($t24) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:456:9+134

    // write_back[voting::VotingForum<#0>@]($t24) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:456:9+134
    $1_voting_VotingForum'$1_governance_proposal_GovernanceProposal'_$memory := $ResourceUpdate($1_voting_VotingForum'$1_governance_proposal_GovernanceProposal'_$memory, $GlobalLocationAddress($t24),
        $Dereference($t24));

    // destroy($t26) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:456:9+134

    // $t46 := 11 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:456:88+53
    $t46 := 11;
    assume $IsValid'u64'($t46);

    // $t47 := error::invalid_argument($t46) on_abort goto L14 with $t23 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:456:64+78
    call $t47 := $1_error_invalid_argument($t46);
    if ($abort_flag) {
        assume {:print "$at(153,24504,24582)"} true;
        $t23 := $abort_code;
        assume {:print "$track_abort(30,18):", $t23} $t23 == $t23;
        goto L14;
    }

    // trace_abort($t47) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:456:9+134
    assume {:print "$at(153,24449,24583)"} true;
    assume {:print "$track_abort(30,18):", $t47} $t47 == $t47;

    // $t23 := move($t47) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:456:9+134
    $t23 := $t47;

    // goto L14 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:456:9+134
    goto L14;

    // label L7 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:462:13+28
    assume {:print "$at(153,24904,24932)"} true;
L7:

    // if ($t44) goto L9 else goto L8 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:462:9+810
    assume {:print "$at(153,24900,25710)"} true;
    if ($t44) { goto L9; } else { goto L8; }

    // label L9 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:463:36+4
    assume {:print "$at(153,24971,24975)"} true;
L9:

    // $t48 := true at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:463:36+4
    assume {:print "$at(153,24971,24975)"} true;
    $t48 := true;
    assume $IsValid'bool'($t48);

    // $t49 := borrow_field<voting::Proposal<#0>>.is_resolved($t26) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:463:13+20
    $t49 := $ChildMutation($t26, 10, $is_resolved#$1_voting_Proposal'$1_governance_proposal_GovernanceProposal'($Dereference($t26)));

    // write_ref($t49, $t48) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:463:13+27
    $t49 := $UpdateMutation($t49, $t48);

    // write_back[Reference($t26).is_resolved (bool)]($t49) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:463:13+27
    $t26 := $UpdateMutation($t26, $Update'$1_voting_Proposal'$1_governance_proposal_GovernanceProposal''_is_resolved($Dereference($t26), $Dereference($t49)));

    // $t50 := timestamp::now_seconds() on_abort goto L14 with $t23 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:464:45+24
    assume {:print "$at(153,25021,25045)"} true;
    call $t50 := $1_timestamp_now_seconds();
    if ($abort_flag) {
        assume {:print "$at(153,25021,25045)"} true;
        $t23 := $abort_code;
        assume {:print "$track_abort(30,18):", $t23} $t23 == $t23;
        goto L14;
    }

    // $t51 := borrow_field<voting::Proposal<#0>>.resolution_time_secs($t26) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:464:13+29
    $t51 := $ChildMutation($t26, 11, $resolution_time_secs#$1_voting_Proposal'$1_governance_proposal_GovernanceProposal'($Dereference($t26)));

    // write_ref($t51, $t50) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:464:13+56
    $t51 := $UpdateMutation($t51, $t50);

    // write_back[Reference($t26).resolution_time_secs (u64)]($t51) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:464:13+56
    $t26 := $UpdateMutation($t26, $Update'$1_voting_Proposal'$1_governance_proposal_GovernanceProposal''_resolution_time_secs($Dereference($t26), $Dereference($t51)));

    // if ($t4) goto L11 else goto L10 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:467:13+255
    assume {:print "$at(153,25210,25465)"} true;
    if ($t4) { goto L11; } else { goto L10; }

    // label L11 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:468:93+8
    assume {:print "$at(153,25323,25331)"} true;
L11:

    // $t52 := borrow_field<voting::Proposal<#0>>.metadata($t26) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:468:88+22
    assume {:print "$at(153,25318,25340)"} true;
    $t52 := $ChildMutation($t26, 2, $metadata#$1_voting_Proposal'$1_governance_proposal_GovernanceProposal'($Dereference($t26)));

    // $t53 := simple_map::borrow_mut<string::String, vector<u8>>($t52, $t28) on_abort goto L14 with $t23 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:468:65+76
    call $t53,$t52 := $1_simple_map_borrow_mut'$1_string_String_vec'u8''($t52, $t28);
    if ($abort_flag) {
        assume {:print "$at(153,25295,25371)"} true;
        $t23 := $abort_code;
        assume {:print "$track_abort(30,18):", $t23} $t23 == $t23;
        goto L14;
    }

    // trace_local[is_multi_step_proposal_in_execution_value#3]($t53) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:468:21+41
    $temp_0'vec'u8'' := $Dereference($t53);
    assume {:print "$track_local(30,18,8):", $temp_0'vec'u8''} $temp_0'vec'u8'' == $temp_0'vec'u8'';

    // $t54 := false at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:469:72+5
    assume {:print "$at(153,25444,25449)"} true;
    $t54 := false;
    assume $IsValid'bool'($t54);

    // $t55 := bcs::to_bytes<bool>($t54) on_abort goto L14 with $t23 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:469:62+16
    call $t55 := $1_bcs_to_bytes'bool'($t54);
    if ($abort_flag) {
        assume {:print "$at(153,25434,25450)"} true;
        $t23 := $abort_code;
        assume {:print "$track_abort(30,18):", $t23} $t23 == $t23;
        goto L14;
    }

    // write_ref($t53, $t55) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:469:17+61
    $t53 := $UpdateMutation($t53, $t55);

    // write_back[Reference($t52)[]]($t53) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:469:17+61
    $t52 := $UpdateMutation($t52, UpdateTable($Dereference($t52), ReadVec(p#$Mutation($t53), LenVec(p#$Mutation($t52))), $Dereference($t53)));

    // write_back[Reference($t26).metadata (simple_map::SimpleMap<string::String, vector<u8>>)]($t52) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:469:17+61
    $t26 := $UpdateMutation($t26, $Update'$1_voting_Proposal'$1_governance_proposal_GovernanceProposal''_metadata($Dereference($t26), $Dereference($t52)));

    // label L10 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:470:14+1
    assume {:print "$at(153,25465,25466)"} true;
L10:

    // goto L12 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:470:14+1
    assume {:print "$at(153,25465,25466)"} true;
    goto L12;

    // label L8 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:474:39+19
    assume {:print "$at(153,25680,25699)"} true;
L8:

    // $t56 := borrow_field<voting::Proposal<#0>>.execution_hash($t26) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:474:13+23
    assume {:print "$at(153,25654,25677)"} true;
    $t56 := $ChildMutation($t26, 4, $execution_hash#$1_voting_Proposal'$1_governance_proposal_GovernanceProposal'($Dereference($t26)));

    // write_ref($t56, $t2) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:474:13+45
    $t56 := $UpdateMutation($t56, $t2);

    // write_back[Reference($t26).execution_hash (vector<u8>)]($t56) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:474:13+45
    $t26 := $UpdateMutation($t26, $Update'$1_voting_Proposal'$1_governance_proposal_GovernanceProposal''_execution_hash($Dereference($t26), $Dereference($t56)));

    // label L12 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:480:52+8
    assume {:print "$at(153,26065,26073)"} true;
L12:

    // $t57 := read_ref($t26) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:480:52+8
    assume {:print "$at(153,26065,26073)"} true;
    $t57 := $Dereference($t26);

    // $t58 := voting::can_be_resolved_early<#0>($t57) on_abort goto L14 with $t23 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:480:30+31
    call $t58 := $1_voting_can_be_resolved_early'$1_governance_proposal_GovernanceProposal'($t57);
    if ($abort_flag) {
        assume {:print "$at(153,26043,26074)"} true;
        $t23 := $abort_code;
        assume {:print "$track_abort(30,18):", $t23} $t23 == $t23;
        goto L14;
    }

    // trace_local[resolved_early]($t58) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:480:13+14
    assume {:print "$track_local(30,18,13):", $t58} $t58 == $t58;

    // $t59 := borrow_field<voting::VotingForum<#0>>.events($t24) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:482:18+19
    assume {:print "$at(153,26137,26156)"} true;
    $t59 := $ChildMutation($t24, 1, $events#$1_voting_VotingForum'$1_governance_proposal_GovernanceProposal'($Dereference($t24)));

    // $t60 := borrow_field<voting::VotingEvents>.resolve_proposal_events($t59) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:482:13+48
    $t60 := $ChildMutation($t59, 2, $resolve_proposal_events#$1_voting_VotingEvents($Dereference($t59)));

    // $t61 := get_field<voting::Proposal<#0>>.yes_votes($t26) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:485:28+18
    assume {:print "$at(153,26268,26286)"} true;
    $t61 := $yes_votes#$1_voting_Proposal'$1_governance_proposal_GovernanceProposal'($Dereference($t26));

    // $t62 := get_field<voting::Proposal<#0>>.no_votes($t26) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:486:27+17
    assume {:print "$at(153,26314,26331)"} true;
    $t62 := $no_votes#$1_voting_Proposal'$1_governance_proposal_GovernanceProposal'($Dereference($t26));

    // write_back[Reference($t25)[]]($t26) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:486:27+17
    $t25 := $UpdateMutation($t25, UpdateTable($Dereference($t25), ReadVec(p#$Mutation($t26), LenVec(p#$Mutation($t25))), $Dereference($t26)));

    // write_back[Reference($t24).proposals (table::Table<u64, voting::Proposal<#0>>)]($t25) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:486:27+17
    $t24 := $UpdateMutation($t24, $Update'$1_voting_VotingForum'$1_governance_proposal_GovernanceProposal''_proposals($Dereference($t24), $Dereference($t25)));

    // $t63 := pack voting::ResolveProposal($t1, $t61, $t62, $t58) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:483:13+184
    assume {:print "$at(153,26194,26378)"} true;
    $t63 := $1_voting_ResolveProposal($t1, $t61, $t62, $t58);

    // opaque begin: event::emit_event<voting::ResolveProposal>($t60, $t63) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:481:9+305
    assume {:print "$at(153,26084,26389)"} true;

    // opaque end: event::emit_event<voting::ResolveProposal>($t60, $t63) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:481:9+305

    // write_back[Reference($t59).resolve_proposal_events (event::EventHandle<voting::ResolveProposal>)]($t60) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:481:9+305
    $t59 := $UpdateMutation($t59, $Update'$1_voting_VotingEvents'_resolve_proposal_events($Dereference($t59), $Dereference($t60)));

    // write_back[Reference($t24).events (voting::VotingEvents)]($t59) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:481:9+305
    $t24 := $UpdateMutation($t24, $Update'$1_voting_VotingForum'$1_governance_proposal_GovernanceProposal''_events($Dereference($t24), $Dereference($t59)));

    // pack_ref_deep($t24) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:481:9+305

    // write_back[voting::VotingForum<#0>@]($t24) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:481:9+305
    $1_voting_VotingForum'$1_governance_proposal_GovernanceProposal'_$memory := $ResourceUpdate($1_voting_VotingForum'$1_governance_proposal_GovernanceProposal'_$memory, $GlobalLocationAddress($t24),
        $Dereference($t24));

    // label L13 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:490:5+1
    assume {:print "$at(153,26395,26396)"} true;
L13:

    // return () at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:490:5+1
    assume {:print "$at(153,26395,26396)"} true;
    return;

    // label L14 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:490:5+1
L14:

    // abort($t23) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:490:5+1
    assume {:print "$at(153,26395,26396)"} true;
    $abort_code := $t23;
    $abort_flag := true;
    return;

}

// struct staking_config::StakingConfig at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/configs/staking_config.move:49:5+1753
type {:datatype} $1_staking_config_StakingConfig;
function {:constructor} $1_staking_config_StakingConfig($minimum_stake: int, $maximum_stake: int, $recurring_lockup_duration_secs: int, $allow_validator_set_change: bool, $rewards_rate: int, $rewards_rate_denominator: int, $voting_power_increase_limit: int): $1_staking_config_StakingConfig;
function {:inline} $Update'$1_staking_config_StakingConfig'_minimum_stake(s: $1_staking_config_StakingConfig, x: int): $1_staking_config_StakingConfig {
    $1_staking_config_StakingConfig(x, $maximum_stake#$1_staking_config_StakingConfig(s), $recurring_lockup_duration_secs#$1_staking_config_StakingConfig(s), $allow_validator_set_change#$1_staking_config_StakingConfig(s), $rewards_rate#$1_staking_config_StakingConfig(s), $rewards_rate_denominator#$1_staking_config_StakingConfig(s), $voting_power_increase_limit#$1_staking_config_StakingConfig(s))
}
function {:inline} $Update'$1_staking_config_StakingConfig'_maximum_stake(s: $1_staking_config_StakingConfig, x: int): $1_staking_config_StakingConfig {
    $1_staking_config_StakingConfig($minimum_stake#$1_staking_config_StakingConfig(s), x, $recurring_lockup_duration_secs#$1_staking_config_StakingConfig(s), $allow_validator_set_change#$1_staking_config_StakingConfig(s), $rewards_rate#$1_staking_config_StakingConfig(s), $rewards_rate_denominator#$1_staking_config_StakingConfig(s), $voting_power_increase_limit#$1_staking_config_StakingConfig(s))
}
function {:inline} $Update'$1_staking_config_StakingConfig'_recurring_lockup_duration_secs(s: $1_staking_config_StakingConfig, x: int): $1_staking_config_StakingConfig {
    $1_staking_config_StakingConfig($minimum_stake#$1_staking_config_StakingConfig(s), $maximum_stake#$1_staking_config_StakingConfig(s), x, $allow_validator_set_change#$1_staking_config_StakingConfig(s), $rewards_rate#$1_staking_config_StakingConfig(s), $rewards_rate_denominator#$1_staking_config_StakingConfig(s), $voting_power_increase_limit#$1_staking_config_StakingConfig(s))
}
function {:inline} $Update'$1_staking_config_StakingConfig'_allow_validator_set_change(s: $1_staking_config_StakingConfig, x: bool): $1_staking_config_StakingConfig {
    $1_staking_config_StakingConfig($minimum_stake#$1_staking_config_StakingConfig(s), $maximum_stake#$1_staking_config_StakingConfig(s), $recurring_lockup_duration_secs#$1_staking_config_StakingConfig(s), x, $rewards_rate#$1_staking_config_StakingConfig(s), $rewards_rate_denominator#$1_staking_config_StakingConfig(s), $voting_power_increase_limit#$1_staking_config_StakingConfig(s))
}
function {:inline} $Update'$1_staking_config_StakingConfig'_rewards_rate(s: $1_staking_config_StakingConfig, x: int): $1_staking_config_StakingConfig {
    $1_staking_config_StakingConfig($minimum_stake#$1_staking_config_StakingConfig(s), $maximum_stake#$1_staking_config_StakingConfig(s), $recurring_lockup_duration_secs#$1_staking_config_StakingConfig(s), $allow_validator_set_change#$1_staking_config_StakingConfig(s), x, $rewards_rate_denominator#$1_staking_config_StakingConfig(s), $voting_power_increase_limit#$1_staking_config_StakingConfig(s))
}
function {:inline} $Update'$1_staking_config_StakingConfig'_rewards_rate_denominator(s: $1_staking_config_StakingConfig, x: int): $1_staking_config_StakingConfig {
    $1_staking_config_StakingConfig($minimum_stake#$1_staking_config_StakingConfig(s), $maximum_stake#$1_staking_config_StakingConfig(s), $recurring_lockup_duration_secs#$1_staking_config_StakingConfig(s), $allow_validator_set_change#$1_staking_config_StakingConfig(s), $rewards_rate#$1_staking_config_StakingConfig(s), x, $voting_power_increase_limit#$1_staking_config_StakingConfig(s))
}
function {:inline} $Update'$1_staking_config_StakingConfig'_voting_power_increase_limit(s: $1_staking_config_StakingConfig, x: int): $1_staking_config_StakingConfig {
    $1_staking_config_StakingConfig($minimum_stake#$1_staking_config_StakingConfig(s), $maximum_stake#$1_staking_config_StakingConfig(s), $recurring_lockup_duration_secs#$1_staking_config_StakingConfig(s), $allow_validator_set_change#$1_staking_config_StakingConfig(s), $rewards_rate#$1_staking_config_StakingConfig(s), $rewards_rate_denominator#$1_staking_config_StakingConfig(s), x)
}
function $IsValid'$1_staking_config_StakingConfig'(s: $1_staking_config_StakingConfig): bool {
    $IsValid'u64'($minimum_stake#$1_staking_config_StakingConfig(s))
      && $IsValid'u64'($maximum_stake#$1_staking_config_StakingConfig(s))
      && $IsValid'u64'($recurring_lockup_duration_secs#$1_staking_config_StakingConfig(s))
      && $IsValid'bool'($allow_validator_set_change#$1_staking_config_StakingConfig(s))
      && $IsValid'u64'($rewards_rate#$1_staking_config_StakingConfig(s))
      && $IsValid'u64'($rewards_rate_denominator#$1_staking_config_StakingConfig(s))
      && $IsValid'u64'($voting_power_increase_limit#$1_staking_config_StakingConfig(s))
}
function {:inline} $IsEqual'$1_staking_config_StakingConfig'(s1: $1_staking_config_StakingConfig, s2: $1_staking_config_StakingConfig): bool {
    s1 == s2
}
var $1_staking_config_StakingConfig_$memory: $Memory $1_staking_config_StakingConfig;

// struct stake::AptosCoinCapabilities at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/stake.move:187:5+89
type {:datatype} $1_stake_AptosCoinCapabilities;
function {:constructor} $1_stake_AptosCoinCapabilities($mint_cap: $1_coin_MintCapability'$1_aptos_coin_AptosCoin'): $1_stake_AptosCoinCapabilities;
function {:inline} $Update'$1_stake_AptosCoinCapabilities'_mint_cap(s: $1_stake_AptosCoinCapabilities, x: $1_coin_MintCapability'$1_aptos_coin_AptosCoin'): $1_stake_AptosCoinCapabilities {
    $1_stake_AptosCoinCapabilities(x)
}
function $IsValid'$1_stake_AptosCoinCapabilities'(s: $1_stake_AptosCoinCapabilities): bool {
    $IsValid'$1_coin_MintCapability'$1_aptos_coin_AptosCoin''($mint_cap#$1_stake_AptosCoinCapabilities(s))
}
function {:inline} $IsEqual'$1_stake_AptosCoinCapabilities'(s1: $1_stake_AptosCoinCapabilities, s2: $1_stake_AptosCoinCapabilities): bool {
    s1 == s2
}
var $1_stake_AptosCoinCapabilities_$memory: $Memory $1_stake_AptosCoinCapabilities;

// struct stake::IndividualValidatorPerformance at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/stake.move:191:5+127
type {:datatype} $1_stake_IndividualValidatorPerformance;
function {:constructor} $1_stake_IndividualValidatorPerformance($successful_proposals: int, $failed_proposals: int): $1_stake_IndividualValidatorPerformance;
function {:inline} $Update'$1_stake_IndividualValidatorPerformance'_successful_proposals(s: $1_stake_IndividualValidatorPerformance, x: int): $1_stake_IndividualValidatorPerformance {
    $1_stake_IndividualValidatorPerformance(x, $failed_proposals#$1_stake_IndividualValidatorPerformance(s))
}
function {:inline} $Update'$1_stake_IndividualValidatorPerformance'_failed_proposals(s: $1_stake_IndividualValidatorPerformance, x: int): $1_stake_IndividualValidatorPerformance {
    $1_stake_IndividualValidatorPerformance($successful_proposals#$1_stake_IndividualValidatorPerformance(s), x)
}
function $IsValid'$1_stake_IndividualValidatorPerformance'(s: $1_stake_IndividualValidatorPerformance): bool {
    $IsValid'u64'($successful_proposals#$1_stake_IndividualValidatorPerformance(s))
      && $IsValid'u64'($failed_proposals#$1_stake_IndividualValidatorPerformance(s))
}
function {:inline} $IsEqual'$1_stake_IndividualValidatorPerformance'(s1: $1_stake_IndividualValidatorPerformance, s2: $1_stake_IndividualValidatorPerformance): bool {
    s1 == s2
}

// struct stake::ValidatorConfig at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/stake.move:151:5+372
type {:datatype} $1_stake_ValidatorConfig;
function {:constructor} $1_stake_ValidatorConfig($consensus_pubkey: Vec (int), $network_addresses: Vec (int), $fullnode_addresses: Vec (int), $validator_index: int): $1_stake_ValidatorConfig;
function {:inline} $Update'$1_stake_ValidatorConfig'_consensus_pubkey(s: $1_stake_ValidatorConfig, x: Vec (int)): $1_stake_ValidatorConfig {
    $1_stake_ValidatorConfig(x, $network_addresses#$1_stake_ValidatorConfig(s), $fullnode_addresses#$1_stake_ValidatorConfig(s), $validator_index#$1_stake_ValidatorConfig(s))
}
function {:inline} $Update'$1_stake_ValidatorConfig'_network_addresses(s: $1_stake_ValidatorConfig, x: Vec (int)): $1_stake_ValidatorConfig {
    $1_stake_ValidatorConfig($consensus_pubkey#$1_stake_ValidatorConfig(s), x, $fullnode_addresses#$1_stake_ValidatorConfig(s), $validator_index#$1_stake_ValidatorConfig(s))
}
function {:inline} $Update'$1_stake_ValidatorConfig'_fullnode_addresses(s: $1_stake_ValidatorConfig, x: Vec (int)): $1_stake_ValidatorConfig {
    $1_stake_ValidatorConfig($consensus_pubkey#$1_stake_ValidatorConfig(s), $network_addresses#$1_stake_ValidatorConfig(s), x, $validator_index#$1_stake_ValidatorConfig(s))
}
function {:inline} $Update'$1_stake_ValidatorConfig'_validator_index(s: $1_stake_ValidatorConfig, x: int): $1_stake_ValidatorConfig {
    $1_stake_ValidatorConfig($consensus_pubkey#$1_stake_ValidatorConfig(s), $network_addresses#$1_stake_ValidatorConfig(s), $fullnode_addresses#$1_stake_ValidatorConfig(s), x)
}
function $IsValid'$1_stake_ValidatorConfig'(s: $1_stake_ValidatorConfig): bool {
    $IsValid'vec'u8''($consensus_pubkey#$1_stake_ValidatorConfig(s))
      && $IsValid'vec'u8''($network_addresses#$1_stake_ValidatorConfig(s))
      && $IsValid'vec'u8''($fullnode_addresses#$1_stake_ValidatorConfig(s))
      && $IsValid'u64'($validator_index#$1_stake_ValidatorConfig(s))
}
function {:inline} $IsEqual'$1_stake_ValidatorConfig'(s1: $1_stake_ValidatorConfig, s2: $1_stake_ValidatorConfig): bool {
    $IsEqual'vec'u8''($consensus_pubkey#$1_stake_ValidatorConfig(s1), $consensus_pubkey#$1_stake_ValidatorConfig(s2))
    && $IsEqual'vec'u8''($network_addresses#$1_stake_ValidatorConfig(s1), $network_addresses#$1_stake_ValidatorConfig(s2))
    && $IsEqual'vec'u8''($fullnode_addresses#$1_stake_ValidatorConfig(s1), $fullnode_addresses#$1_stake_ValidatorConfig(s2))
    && $IsEqual'u64'($validator_index#$1_stake_ValidatorConfig(s1), $validator_index#$1_stake_ValidatorConfig(s2))}
var $1_stake_ValidatorConfig_$memory: $Memory $1_stake_ValidatorConfig;

// struct stake::ValidatorInfo at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/stake.move:161:5+133
type {:datatype} $1_stake_ValidatorInfo;
function {:constructor} $1_stake_ValidatorInfo($addr: int, $voting_power: int, $config: $1_stake_ValidatorConfig): $1_stake_ValidatorInfo;
function {:inline} $Update'$1_stake_ValidatorInfo'_addr(s: $1_stake_ValidatorInfo, x: int): $1_stake_ValidatorInfo {
    $1_stake_ValidatorInfo(x, $voting_power#$1_stake_ValidatorInfo(s), $config#$1_stake_ValidatorInfo(s))
}
function {:inline} $Update'$1_stake_ValidatorInfo'_voting_power(s: $1_stake_ValidatorInfo, x: int): $1_stake_ValidatorInfo {
    $1_stake_ValidatorInfo($addr#$1_stake_ValidatorInfo(s), x, $config#$1_stake_ValidatorInfo(s))
}
function {:inline} $Update'$1_stake_ValidatorInfo'_config(s: $1_stake_ValidatorInfo, x: $1_stake_ValidatorConfig): $1_stake_ValidatorInfo {
    $1_stake_ValidatorInfo($addr#$1_stake_ValidatorInfo(s), $voting_power#$1_stake_ValidatorInfo(s), x)
}
function $IsValid'$1_stake_ValidatorInfo'(s: $1_stake_ValidatorInfo): bool {
    $IsValid'address'($addr#$1_stake_ValidatorInfo(s))
      && $IsValid'u64'($voting_power#$1_stake_ValidatorInfo(s))
      && $IsValid'$1_stake_ValidatorConfig'($config#$1_stake_ValidatorInfo(s))
}
function {:inline} $IsEqual'$1_stake_ValidatorInfo'(s1: $1_stake_ValidatorInfo, s2: $1_stake_ValidatorInfo): bool {
    $IsEqual'address'($addr#$1_stake_ValidatorInfo(s1), $addr#$1_stake_ValidatorInfo(s2))
    && $IsEqual'u64'($voting_power#$1_stake_ValidatorInfo(s1), $voting_power#$1_stake_ValidatorInfo(s2))
    && $IsEqual'$1_stake_ValidatorConfig'($config#$1_stake_ValidatorInfo(s1), $config#$1_stake_ValidatorInfo(s2))}

// struct stake::ValidatorPerformance at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/stake.move:196:5+103
type {:datatype} $1_stake_ValidatorPerformance;
function {:constructor} $1_stake_ValidatorPerformance($validators: Vec ($1_stake_IndividualValidatorPerformance)): $1_stake_ValidatorPerformance;
function {:inline} $Update'$1_stake_ValidatorPerformance'_validators(s: $1_stake_ValidatorPerformance, x: Vec ($1_stake_IndividualValidatorPerformance)): $1_stake_ValidatorPerformance {
    $1_stake_ValidatorPerformance(x)
}
function $IsValid'$1_stake_ValidatorPerformance'(s: $1_stake_ValidatorPerformance): bool {
    $IsValid'vec'$1_stake_IndividualValidatorPerformance''($validators#$1_stake_ValidatorPerformance(s))
}
function {:inline} $IsEqual'$1_stake_ValidatorPerformance'(s1: $1_stake_ValidatorPerformance, s2: $1_stake_ValidatorPerformance): bool {
    $IsEqual'vec'$1_stake_IndividualValidatorPerformance''($validators#$1_stake_ValidatorPerformance(s1), $validators#$1_stake_ValidatorPerformance(s2))}
var $1_stake_ValidatorPerformance_$memory: $Memory $1_stake_ValidatorPerformance;

// struct stake::ValidatorSet at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/stake.move:171:5+558
type {:datatype} $1_stake_ValidatorSet;
function {:constructor} $1_stake_ValidatorSet($consensus_scheme: int, $active_validators: Vec ($1_stake_ValidatorInfo), $pending_inactive: Vec ($1_stake_ValidatorInfo), $pending_active: Vec ($1_stake_ValidatorInfo), $total_voting_power: int, $total_joining_power: int): $1_stake_ValidatorSet;
function {:inline} $Update'$1_stake_ValidatorSet'_consensus_scheme(s: $1_stake_ValidatorSet, x: int): $1_stake_ValidatorSet {
    $1_stake_ValidatorSet(x, $active_validators#$1_stake_ValidatorSet(s), $pending_inactive#$1_stake_ValidatorSet(s), $pending_active#$1_stake_ValidatorSet(s), $total_voting_power#$1_stake_ValidatorSet(s), $total_joining_power#$1_stake_ValidatorSet(s))
}
function {:inline} $Update'$1_stake_ValidatorSet'_active_validators(s: $1_stake_ValidatorSet, x: Vec ($1_stake_ValidatorInfo)): $1_stake_ValidatorSet {
    $1_stake_ValidatorSet($consensus_scheme#$1_stake_ValidatorSet(s), x, $pending_inactive#$1_stake_ValidatorSet(s), $pending_active#$1_stake_ValidatorSet(s), $total_voting_power#$1_stake_ValidatorSet(s), $total_joining_power#$1_stake_ValidatorSet(s))
}
function {:inline} $Update'$1_stake_ValidatorSet'_pending_inactive(s: $1_stake_ValidatorSet, x: Vec ($1_stake_ValidatorInfo)): $1_stake_ValidatorSet {
    $1_stake_ValidatorSet($consensus_scheme#$1_stake_ValidatorSet(s), $active_validators#$1_stake_ValidatorSet(s), x, $pending_active#$1_stake_ValidatorSet(s), $total_voting_power#$1_stake_ValidatorSet(s), $total_joining_power#$1_stake_ValidatorSet(s))
}
function {:inline} $Update'$1_stake_ValidatorSet'_pending_active(s: $1_stake_ValidatorSet, x: Vec ($1_stake_ValidatorInfo)): $1_stake_ValidatorSet {
    $1_stake_ValidatorSet($consensus_scheme#$1_stake_ValidatorSet(s), $active_validators#$1_stake_ValidatorSet(s), $pending_inactive#$1_stake_ValidatorSet(s), x, $total_voting_power#$1_stake_ValidatorSet(s), $total_joining_power#$1_stake_ValidatorSet(s))
}
function {:inline} $Update'$1_stake_ValidatorSet'_total_voting_power(s: $1_stake_ValidatorSet, x: int): $1_stake_ValidatorSet {
    $1_stake_ValidatorSet($consensus_scheme#$1_stake_ValidatorSet(s), $active_validators#$1_stake_ValidatorSet(s), $pending_inactive#$1_stake_ValidatorSet(s), $pending_active#$1_stake_ValidatorSet(s), x, $total_joining_power#$1_stake_ValidatorSet(s))
}
function {:inline} $Update'$1_stake_ValidatorSet'_total_joining_power(s: $1_stake_ValidatorSet, x: int): $1_stake_ValidatorSet {
    $1_stake_ValidatorSet($consensus_scheme#$1_stake_ValidatorSet(s), $active_validators#$1_stake_ValidatorSet(s), $pending_inactive#$1_stake_ValidatorSet(s), $pending_active#$1_stake_ValidatorSet(s), $total_voting_power#$1_stake_ValidatorSet(s), x)
}
function $IsValid'$1_stake_ValidatorSet'(s: $1_stake_ValidatorSet): bool {
    $IsValid'u8'($consensus_scheme#$1_stake_ValidatorSet(s))
      && $IsValid'vec'$1_stake_ValidatorInfo''($active_validators#$1_stake_ValidatorSet(s))
      && $IsValid'vec'$1_stake_ValidatorInfo''($pending_inactive#$1_stake_ValidatorSet(s))
      && $IsValid'vec'$1_stake_ValidatorInfo''($pending_active#$1_stake_ValidatorSet(s))
      && $IsValid'u128'($total_voting_power#$1_stake_ValidatorSet(s))
      && $IsValid'u128'($total_joining_power#$1_stake_ValidatorSet(s))
}
function {:inline} $IsEqual'$1_stake_ValidatorSet'(s1: $1_stake_ValidatorSet, s2: $1_stake_ValidatorSet): bool {
    $IsEqual'u8'($consensus_scheme#$1_stake_ValidatorSet(s1), $consensus_scheme#$1_stake_ValidatorSet(s2))
    && $IsEqual'vec'$1_stake_ValidatorInfo''($active_validators#$1_stake_ValidatorSet(s1), $active_validators#$1_stake_ValidatorSet(s2))
    && $IsEqual'vec'$1_stake_ValidatorInfo''($pending_inactive#$1_stake_ValidatorSet(s1), $pending_inactive#$1_stake_ValidatorSet(s2))
    && $IsEqual'vec'$1_stake_ValidatorInfo''($pending_active#$1_stake_ValidatorSet(s1), $pending_active#$1_stake_ValidatorSet(s2))
    && $IsEqual'u128'($total_voting_power#$1_stake_ValidatorSet(s1), $total_voting_power#$1_stake_ValidatorSet(s2))
    && $IsEqual'u128'($total_joining_power#$1_stake_ValidatorSet(s1), $total_joining_power#$1_stake_ValidatorSet(s2))}
var $1_stake_ValidatorSet_$memory: $Memory $1_stake_ValidatorSet;

// struct transaction_fee::AptosCoinCapabilities at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/transaction_fee.move:23:5+89
type {:datatype} $1_transaction_fee_AptosCoinCapabilities;
function {:constructor} $1_transaction_fee_AptosCoinCapabilities($burn_cap: $1_coin_BurnCapability'$1_aptos_coin_AptosCoin'): $1_transaction_fee_AptosCoinCapabilities;
function {:inline} $Update'$1_transaction_fee_AptosCoinCapabilities'_burn_cap(s: $1_transaction_fee_AptosCoinCapabilities, x: $1_coin_BurnCapability'$1_aptos_coin_AptosCoin'): $1_transaction_fee_AptosCoinCapabilities {
    $1_transaction_fee_AptosCoinCapabilities(x)
}
function $IsValid'$1_transaction_fee_AptosCoinCapabilities'(s: $1_transaction_fee_AptosCoinCapabilities): bool {
    $IsValid'$1_coin_BurnCapability'$1_aptos_coin_AptosCoin''($burn_cap#$1_transaction_fee_AptosCoinCapabilities(s))
}
function {:inline} $IsEqual'$1_transaction_fee_AptosCoinCapabilities'(s1: $1_transaction_fee_AptosCoinCapabilities, s2: $1_transaction_fee_AptosCoinCapabilities): bool {
    s1 == s2
}
var $1_transaction_fee_AptosCoinCapabilities_$memory: $Memory $1_transaction_fee_AptosCoinCapabilities;

// struct state_storage::GasParameter at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/state_storage.move:83:5+64
type {:datatype} $1_state_storage_GasParameter;
function {:constructor} $1_state_storage_GasParameter($usage: $1_state_storage_Usage): $1_state_storage_GasParameter;
function {:inline} $Update'$1_state_storage_GasParameter'_usage(s: $1_state_storage_GasParameter, x: $1_state_storage_Usage): $1_state_storage_GasParameter {
    $1_state_storage_GasParameter(x)
}
function $IsValid'$1_state_storage_GasParameter'(s: $1_state_storage_GasParameter): bool {
    $IsValid'$1_state_storage_Usage'($usage#$1_state_storage_GasParameter(s))
}
function {:inline} $IsEqual'$1_state_storage_GasParameter'(s1: $1_state_storage_GasParameter, s2: $1_state_storage_GasParameter): bool {
    s1 == s2
}
var $1_state_storage_GasParameter_$memory: $Memory $1_state_storage_GasParameter;

// struct state_storage::StateStorageUsage at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/state_storage.move:19:5+89
type {:datatype} $1_state_storage_StateStorageUsage;
function {:constructor} $1_state_storage_StateStorageUsage($epoch: int, $usage: $1_state_storage_Usage): $1_state_storage_StateStorageUsage;
function {:inline} $Update'$1_state_storage_StateStorageUsage'_epoch(s: $1_state_storage_StateStorageUsage, x: int): $1_state_storage_StateStorageUsage {
    $1_state_storage_StateStorageUsage(x, $usage#$1_state_storage_StateStorageUsage(s))
}
function {:inline} $Update'$1_state_storage_StateStorageUsage'_usage(s: $1_state_storage_StateStorageUsage, x: $1_state_storage_Usage): $1_state_storage_StateStorageUsage {
    $1_state_storage_StateStorageUsage($epoch#$1_state_storage_StateStorageUsage(s), x)
}
function $IsValid'$1_state_storage_StateStorageUsage'(s: $1_state_storage_StateStorageUsage): bool {
    $IsValid'u64'($epoch#$1_state_storage_StateStorageUsage(s))
      && $IsValid'$1_state_storage_Usage'($usage#$1_state_storage_StateStorageUsage(s))
}
function {:inline} $IsEqual'$1_state_storage_StateStorageUsage'(s1: $1_state_storage_StateStorageUsage, s2: $1_state_storage_StateStorageUsage): bool {
    s1 == s2
}
var $1_state_storage_StateStorageUsage_$memory: $Memory $1_state_storage_StateStorageUsage;

// struct state_storage::Usage at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/state_storage.move:12:5+82
type {:datatype} $1_state_storage_Usage;
function {:constructor} $1_state_storage_Usage($items: int, $bytes: int): $1_state_storage_Usage;
function {:inline} $Update'$1_state_storage_Usage'_items(s: $1_state_storage_Usage, x: int): $1_state_storage_Usage {
    $1_state_storage_Usage(x, $bytes#$1_state_storage_Usage(s))
}
function {:inline} $Update'$1_state_storage_Usage'_bytes(s: $1_state_storage_Usage, x: int): $1_state_storage_Usage {
    $1_state_storage_Usage($items#$1_state_storage_Usage(s), x)
}
function $IsValid'$1_state_storage_Usage'(s: $1_state_storage_Usage): bool {
    $IsValid'u64'($items#$1_state_storage_Usage(s))
      && $IsValid'u64'($bytes#$1_state_storage_Usage(s))
}
function {:inline} $IsEqual'$1_state_storage_Usage'(s1: $1_state_storage_Usage, s2: $1_state_storage_Usage): bool {
    s1 == s2
}

// struct storage_gas::GasCurve at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/storage_gas.move:247:5+120
type {:datatype} $1_storage_gas_GasCurve;
function {:constructor} $1_storage_gas_GasCurve($min_gas: int, $max_gas: int, $points: Vec ($1_storage_gas_Point)): $1_storage_gas_GasCurve;
function {:inline} $Update'$1_storage_gas_GasCurve'_min_gas(s: $1_storage_gas_GasCurve, x: int): $1_storage_gas_GasCurve {
    $1_storage_gas_GasCurve(x, $max_gas#$1_storage_gas_GasCurve(s), $points#$1_storage_gas_GasCurve(s))
}
function {:inline} $Update'$1_storage_gas_GasCurve'_max_gas(s: $1_storage_gas_GasCurve, x: int): $1_storage_gas_GasCurve {
    $1_storage_gas_GasCurve($min_gas#$1_storage_gas_GasCurve(s), x, $points#$1_storage_gas_GasCurve(s))
}
function {:inline} $Update'$1_storage_gas_GasCurve'_points(s: $1_storage_gas_GasCurve, x: Vec ($1_storage_gas_Point)): $1_storage_gas_GasCurve {
    $1_storage_gas_GasCurve($min_gas#$1_storage_gas_GasCurve(s), $max_gas#$1_storage_gas_GasCurve(s), x)
}
function $IsValid'$1_storage_gas_GasCurve'(s: $1_storage_gas_GasCurve): bool {
    $IsValid'u64'($min_gas#$1_storage_gas_GasCurve(s))
      && $IsValid'u64'($max_gas#$1_storage_gas_GasCurve(s))
      && $IsValid'vec'$1_storage_gas_Point''($points#$1_storage_gas_GasCurve(s))
}
function {:inline} $IsEqual'$1_storage_gas_GasCurve'(s1: $1_storage_gas_GasCurve, s2: $1_storage_gas_GasCurve): bool {
    $IsEqual'u64'($min_gas#$1_storage_gas_GasCurve(s1), $min_gas#$1_storage_gas_GasCurve(s2))
    && $IsEqual'u64'($max_gas#$1_storage_gas_GasCurve(s1), $max_gas#$1_storage_gas_GasCurve(s2))
    && $IsEqual'vec'$1_storage_gas_Point''($points#$1_storage_gas_GasCurve(s1), $points#$1_storage_gas_GasCurve(s2))}

// struct storage_gas::Point at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/storage_gas.move:207:5+322
type {:datatype} $1_storage_gas_Point;
function {:constructor} $1_storage_gas_Point($x: int, $y: int): $1_storage_gas_Point;
function {:inline} $Update'$1_storage_gas_Point'_x(s: $1_storage_gas_Point, x: int): $1_storage_gas_Point {
    $1_storage_gas_Point(x, $y#$1_storage_gas_Point(s))
}
function {:inline} $Update'$1_storage_gas_Point'_y(s: $1_storage_gas_Point, x: int): $1_storage_gas_Point {
    $1_storage_gas_Point($x#$1_storage_gas_Point(s), x)
}
function $IsValid'$1_storage_gas_Point'(s: $1_storage_gas_Point): bool {
    $IsValid'u64'($x#$1_storage_gas_Point(s))
      && $IsValid'u64'($y#$1_storage_gas_Point(s))
}
function {:inline} $IsEqual'$1_storage_gas_Point'(s1: $1_storage_gas_Point, s2: $1_storage_gas_Point): bool {
    s1 == s2
}

// struct storage_gas::StorageGas at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/storage_gas.move:183:5+534
type {:datatype} $1_storage_gas_StorageGas;
function {:constructor} $1_storage_gas_StorageGas($per_item_read: int, $per_item_create: int, $per_item_write: int, $per_byte_read: int, $per_byte_create: int, $per_byte_write: int): $1_storage_gas_StorageGas;
function {:inline} $Update'$1_storage_gas_StorageGas'_per_item_read(s: $1_storage_gas_StorageGas, x: int): $1_storage_gas_StorageGas {
    $1_storage_gas_StorageGas(x, $per_item_create#$1_storage_gas_StorageGas(s), $per_item_write#$1_storage_gas_StorageGas(s), $per_byte_read#$1_storage_gas_StorageGas(s), $per_byte_create#$1_storage_gas_StorageGas(s), $per_byte_write#$1_storage_gas_StorageGas(s))
}
function {:inline} $Update'$1_storage_gas_StorageGas'_per_item_create(s: $1_storage_gas_StorageGas, x: int): $1_storage_gas_StorageGas {
    $1_storage_gas_StorageGas($per_item_read#$1_storage_gas_StorageGas(s), x, $per_item_write#$1_storage_gas_StorageGas(s), $per_byte_read#$1_storage_gas_StorageGas(s), $per_byte_create#$1_storage_gas_StorageGas(s), $per_byte_write#$1_storage_gas_StorageGas(s))
}
function {:inline} $Update'$1_storage_gas_StorageGas'_per_item_write(s: $1_storage_gas_StorageGas, x: int): $1_storage_gas_StorageGas {
    $1_storage_gas_StorageGas($per_item_read#$1_storage_gas_StorageGas(s), $per_item_create#$1_storage_gas_StorageGas(s), x, $per_byte_read#$1_storage_gas_StorageGas(s), $per_byte_create#$1_storage_gas_StorageGas(s), $per_byte_write#$1_storage_gas_StorageGas(s))
}
function {:inline} $Update'$1_storage_gas_StorageGas'_per_byte_read(s: $1_storage_gas_StorageGas, x: int): $1_storage_gas_StorageGas {
    $1_storage_gas_StorageGas($per_item_read#$1_storage_gas_StorageGas(s), $per_item_create#$1_storage_gas_StorageGas(s), $per_item_write#$1_storage_gas_StorageGas(s), x, $per_byte_create#$1_storage_gas_StorageGas(s), $per_byte_write#$1_storage_gas_StorageGas(s))
}
function {:inline} $Update'$1_storage_gas_StorageGas'_per_byte_create(s: $1_storage_gas_StorageGas, x: int): $1_storage_gas_StorageGas {
    $1_storage_gas_StorageGas($per_item_read#$1_storage_gas_StorageGas(s), $per_item_create#$1_storage_gas_StorageGas(s), $per_item_write#$1_storage_gas_StorageGas(s), $per_byte_read#$1_storage_gas_StorageGas(s), x, $per_byte_write#$1_storage_gas_StorageGas(s))
}
function {:inline} $Update'$1_storage_gas_StorageGas'_per_byte_write(s: $1_storage_gas_StorageGas, x: int): $1_storage_gas_StorageGas {
    $1_storage_gas_StorageGas($per_item_read#$1_storage_gas_StorageGas(s), $per_item_create#$1_storage_gas_StorageGas(s), $per_item_write#$1_storage_gas_StorageGas(s), $per_byte_read#$1_storage_gas_StorageGas(s), $per_byte_create#$1_storage_gas_StorageGas(s), x)
}
function $IsValid'$1_storage_gas_StorageGas'(s: $1_storage_gas_StorageGas): bool {
    $IsValid'u64'($per_item_read#$1_storage_gas_StorageGas(s))
      && $IsValid'u64'($per_item_create#$1_storage_gas_StorageGas(s))
      && $IsValid'u64'($per_item_write#$1_storage_gas_StorageGas(s))
      && $IsValid'u64'($per_byte_read#$1_storage_gas_StorageGas(s))
      && $IsValid'u64'($per_byte_create#$1_storage_gas_StorageGas(s))
      && $IsValid'u64'($per_byte_write#$1_storage_gas_StorageGas(s))
}
function {:inline} $IsEqual'$1_storage_gas_StorageGas'(s1: $1_storage_gas_StorageGas, s2: $1_storage_gas_StorageGas): bool {
    s1 == s2
}
var $1_storage_gas_StorageGas_$memory: $Memory $1_storage_gas_StorageGas;

// struct storage_gas::StorageGasConfig at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/storage_gas.move:319:5+205
type {:datatype} $1_storage_gas_StorageGasConfig;
function {:constructor} $1_storage_gas_StorageGasConfig($item_config: $1_storage_gas_UsageGasConfig, $byte_config: $1_storage_gas_UsageGasConfig): $1_storage_gas_StorageGasConfig;
function {:inline} $Update'$1_storage_gas_StorageGasConfig'_item_config(s: $1_storage_gas_StorageGasConfig, x: $1_storage_gas_UsageGasConfig): $1_storage_gas_StorageGasConfig {
    $1_storage_gas_StorageGasConfig(x, $byte_config#$1_storage_gas_StorageGasConfig(s))
}
function {:inline} $Update'$1_storage_gas_StorageGasConfig'_byte_config(s: $1_storage_gas_StorageGasConfig, x: $1_storage_gas_UsageGasConfig): $1_storage_gas_StorageGasConfig {
    $1_storage_gas_StorageGasConfig($item_config#$1_storage_gas_StorageGasConfig(s), x)
}
function $IsValid'$1_storage_gas_StorageGasConfig'(s: $1_storage_gas_StorageGasConfig): bool {
    $IsValid'$1_storage_gas_UsageGasConfig'($item_config#$1_storage_gas_StorageGasConfig(s))
      && $IsValid'$1_storage_gas_UsageGasConfig'($byte_config#$1_storage_gas_StorageGasConfig(s))
}
function {:inline} $IsEqual'$1_storage_gas_StorageGasConfig'(s1: $1_storage_gas_StorageGasConfig, s2: $1_storage_gas_StorageGasConfig): bool {
    $IsEqual'$1_storage_gas_UsageGasConfig'($item_config#$1_storage_gas_StorageGasConfig(s1), $item_config#$1_storage_gas_StorageGasConfig(s2))
    && $IsEqual'$1_storage_gas_UsageGasConfig'($byte_config#$1_storage_gas_StorageGasConfig(s1), $byte_config#$1_storage_gas_StorageGasConfig(s2))}
var $1_storage_gas_StorageGasConfig_$memory: $Memory $1_storage_gas_StorageGasConfig;

// struct storage_gas::UsageGasConfig at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/storage_gas.move:221:5+171
type {:datatype} $1_storage_gas_UsageGasConfig;
function {:constructor} $1_storage_gas_UsageGasConfig($target_usage: int, $read_curve: $1_storage_gas_GasCurve, $create_curve: $1_storage_gas_GasCurve, $write_curve: $1_storage_gas_GasCurve): $1_storage_gas_UsageGasConfig;
function {:inline} $Update'$1_storage_gas_UsageGasConfig'_target_usage(s: $1_storage_gas_UsageGasConfig, x: int): $1_storage_gas_UsageGasConfig {
    $1_storage_gas_UsageGasConfig(x, $read_curve#$1_storage_gas_UsageGasConfig(s), $create_curve#$1_storage_gas_UsageGasConfig(s), $write_curve#$1_storage_gas_UsageGasConfig(s))
}
function {:inline} $Update'$1_storage_gas_UsageGasConfig'_read_curve(s: $1_storage_gas_UsageGasConfig, x: $1_storage_gas_GasCurve): $1_storage_gas_UsageGasConfig {
    $1_storage_gas_UsageGasConfig($target_usage#$1_storage_gas_UsageGasConfig(s), x, $create_curve#$1_storage_gas_UsageGasConfig(s), $write_curve#$1_storage_gas_UsageGasConfig(s))
}
function {:inline} $Update'$1_storage_gas_UsageGasConfig'_create_curve(s: $1_storage_gas_UsageGasConfig, x: $1_storage_gas_GasCurve): $1_storage_gas_UsageGasConfig {
    $1_storage_gas_UsageGasConfig($target_usage#$1_storage_gas_UsageGasConfig(s), $read_curve#$1_storage_gas_UsageGasConfig(s), x, $write_curve#$1_storage_gas_UsageGasConfig(s))
}
function {:inline} $Update'$1_storage_gas_UsageGasConfig'_write_curve(s: $1_storage_gas_UsageGasConfig, x: $1_storage_gas_GasCurve): $1_storage_gas_UsageGasConfig {
    $1_storage_gas_UsageGasConfig($target_usage#$1_storage_gas_UsageGasConfig(s), $read_curve#$1_storage_gas_UsageGasConfig(s), $create_curve#$1_storage_gas_UsageGasConfig(s), x)
}
function $IsValid'$1_storage_gas_UsageGasConfig'(s: $1_storage_gas_UsageGasConfig): bool {
    $IsValid'u64'($target_usage#$1_storage_gas_UsageGasConfig(s))
      && $IsValid'$1_storage_gas_GasCurve'($read_curve#$1_storage_gas_UsageGasConfig(s))
      && $IsValid'$1_storage_gas_GasCurve'($create_curve#$1_storage_gas_UsageGasConfig(s))
      && $IsValid'$1_storage_gas_GasCurve'($write_curve#$1_storage_gas_UsageGasConfig(s))
}
function {:inline} $IsEqual'$1_storage_gas_UsageGasConfig'(s1: $1_storage_gas_UsageGasConfig, s2: $1_storage_gas_UsageGasConfig): bool {
    $IsEqual'u64'($target_usage#$1_storage_gas_UsageGasConfig(s1), $target_usage#$1_storage_gas_UsageGasConfig(s2))
    && $IsEqual'$1_storage_gas_GasCurve'($read_curve#$1_storage_gas_UsageGasConfig(s1), $read_curve#$1_storage_gas_UsageGasConfig(s2))
    && $IsEqual'$1_storage_gas_GasCurve'($create_curve#$1_storage_gas_UsageGasConfig(s1), $create_curve#$1_storage_gas_UsageGasConfig(s2))
    && $IsEqual'$1_storage_gas_GasCurve'($write_curve#$1_storage_gas_UsageGasConfig(s1), $write_curve#$1_storage_gas_UsageGasConfig(s2))}

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/reconfiguration.move:154:5+155
function {:inline} $1_reconfiguration_$last_reconfiguration_time($1_reconfiguration_Configuration_$memory: $Memory $1_reconfiguration_Configuration): int {
    $last_reconfiguration_time#$1_reconfiguration_Configuration($ResourceValue($1_reconfiguration_Configuration_$memory, 1))
}

// struct reconfiguration::Configuration at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/reconfiguration.move:33:5+306
type {:datatype} $1_reconfiguration_Configuration;
function {:constructor} $1_reconfiguration_Configuration($epoch: int, $last_reconfiguration_time: int, $events: $1_event_EventHandle'$1_reconfiguration_NewEpochEvent'): $1_reconfiguration_Configuration;
function {:inline} $Update'$1_reconfiguration_Configuration'_epoch(s: $1_reconfiguration_Configuration, x: int): $1_reconfiguration_Configuration {
    $1_reconfiguration_Configuration(x, $last_reconfiguration_time#$1_reconfiguration_Configuration(s), $events#$1_reconfiguration_Configuration(s))
}
function {:inline} $Update'$1_reconfiguration_Configuration'_last_reconfiguration_time(s: $1_reconfiguration_Configuration, x: int): $1_reconfiguration_Configuration {
    $1_reconfiguration_Configuration($epoch#$1_reconfiguration_Configuration(s), x, $events#$1_reconfiguration_Configuration(s))
}
function {:inline} $Update'$1_reconfiguration_Configuration'_events(s: $1_reconfiguration_Configuration, x: $1_event_EventHandle'$1_reconfiguration_NewEpochEvent'): $1_reconfiguration_Configuration {
    $1_reconfiguration_Configuration($epoch#$1_reconfiguration_Configuration(s), $last_reconfiguration_time#$1_reconfiguration_Configuration(s), x)
}
function $IsValid'$1_reconfiguration_Configuration'(s: $1_reconfiguration_Configuration): bool {
    $IsValid'u64'($epoch#$1_reconfiguration_Configuration(s))
      && $IsValid'u64'($last_reconfiguration_time#$1_reconfiguration_Configuration(s))
      && $IsValid'$1_event_EventHandle'$1_reconfiguration_NewEpochEvent''($events#$1_reconfiguration_Configuration(s))
}
function {:inline} $IsEqual'$1_reconfiguration_Configuration'(s1: $1_reconfiguration_Configuration, s2: $1_reconfiguration_Configuration): bool {
    s1 == s2
}
var $1_reconfiguration_Configuration_$memory: $Memory $1_reconfiguration_Configuration;

// struct reconfiguration::NewEpochEvent at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/reconfiguration.move:28:5+64
type {:datatype} $1_reconfiguration_NewEpochEvent;
function {:constructor} $1_reconfiguration_NewEpochEvent($epoch: int): $1_reconfiguration_NewEpochEvent;
function {:inline} $Update'$1_reconfiguration_NewEpochEvent'_epoch(s: $1_reconfiguration_NewEpochEvent, x: int): $1_reconfiguration_NewEpochEvent {
    $1_reconfiguration_NewEpochEvent(x)
}
function $IsValid'$1_reconfiguration_NewEpochEvent'(s: $1_reconfiguration_NewEpochEvent): bool {
    $IsValid'u64'($epoch#$1_reconfiguration_NewEpochEvent(s))
}
function {:inline} $IsEqual'$1_reconfiguration_NewEpochEvent'(s1: $1_reconfiguration_NewEpochEvent, s2: $1_reconfiguration_NewEpochEvent): bool {
    s1 == s2
}

// struct governance_proposal::GovernanceProposal at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/governance_proposal.move:7:5+44
type {:datatype} $1_governance_proposal_GovernanceProposal;
function {:constructor} $1_governance_proposal_GovernanceProposal($dummy_field: bool): $1_governance_proposal_GovernanceProposal;
function {:inline} $Update'$1_governance_proposal_GovernanceProposal'_dummy_field(s: $1_governance_proposal_GovernanceProposal, x: bool): $1_governance_proposal_GovernanceProposal {
    $1_governance_proposal_GovernanceProposal(x)
}
function $IsValid'$1_governance_proposal_GovernanceProposal'(s: $1_governance_proposal_GovernanceProposal): bool {
    $IsValid'bool'($dummy_field#$1_governance_proposal_GovernanceProposal(s))
}
function {:inline} $IsEqual'$1_governance_proposal_GovernanceProposal'(s1: $1_governance_proposal_GovernanceProposal, s2: $1_governance_proposal_GovernanceProposal): bool {
    s1 == s2
}

// struct aptos_governance::ApprovedExecutionHashes at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:88:5+90
type {:datatype} $1_aptos_governance_ApprovedExecutionHashes;
function {:constructor} $1_aptos_governance_ApprovedExecutionHashes($hashes: Table int (Vec (int))): $1_aptos_governance_ApprovedExecutionHashes;
function {:inline} $Update'$1_aptos_governance_ApprovedExecutionHashes'_hashes(s: $1_aptos_governance_ApprovedExecutionHashes, x: Table int (Vec (int))): $1_aptos_governance_ApprovedExecutionHashes {
    $1_aptos_governance_ApprovedExecutionHashes(x)
}
function $IsValid'$1_aptos_governance_ApprovedExecutionHashes'(s: $1_aptos_governance_ApprovedExecutionHashes): bool {
    $IsValid'$1_simple_map_SimpleMap'u64_vec'u8'''($hashes#$1_aptos_governance_ApprovedExecutionHashes(s))
}
function {:inline} $IsEqual'$1_aptos_governance_ApprovedExecutionHashes'(s1: $1_aptos_governance_ApprovedExecutionHashes, s2: $1_aptos_governance_ApprovedExecutionHashes): bool {
    $IsEqual'$1_simple_map_SimpleMap'u64_vec'u8'''($hashes#$1_aptos_governance_ApprovedExecutionHashes(s1), $hashes#$1_aptos_governance_ApprovedExecutionHashes(s2))}
var $1_aptos_governance_ApprovedExecutionHashes_$memory: $Memory $1_aptos_governance_ApprovedExecutionHashes;

// struct aptos_governance::GovernanceResponsbility at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:64:5+105
type {:datatype} $1_aptos_governance_GovernanceResponsbility;
function {:constructor} $1_aptos_governance_GovernanceResponsbility($signer_caps: Table int ($1_account_SignerCapability)): $1_aptos_governance_GovernanceResponsbility;
function {:inline} $Update'$1_aptos_governance_GovernanceResponsbility'_signer_caps(s: $1_aptos_governance_GovernanceResponsbility, x: Table int ($1_account_SignerCapability)): $1_aptos_governance_GovernanceResponsbility {
    $1_aptos_governance_GovernanceResponsbility(x)
}
function $IsValid'$1_aptos_governance_GovernanceResponsbility'(s: $1_aptos_governance_GovernanceResponsbility): bool {
    $IsValid'$1_simple_map_SimpleMap'address_$1_account_SignerCapability''($signer_caps#$1_aptos_governance_GovernanceResponsbility(s))
}
function {:inline} $IsEqual'$1_aptos_governance_GovernanceResponsbility'(s1: $1_aptos_governance_GovernanceResponsbility, s2: $1_aptos_governance_GovernanceResponsbility): bool {
    $IsEqual'$1_simple_map_SimpleMap'address_$1_account_SignerCapability''($signer_caps#$1_aptos_governance_GovernanceResponsbility(s1), $signer_caps#$1_aptos_governance_GovernanceResponsbility(s2))}
var $1_aptos_governance_GovernanceResponsbility_$memory: $Memory $1_aptos_governance_GovernanceResponsbility;

// fun aptos_governance::add_approved_script_hash [baseline] at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:369:5+1139
procedure {:inline 1} $1_aptos_governance_add_approved_script_hash(_$t0: int) returns ()
{
    // declare local variables
    var $t1: $Mutation ($1_aptos_governance_ApprovedExecutionHashes);
    var $t2: $Mutation (Vec (int));
    var $t3: Vec (int);
    var $t4: $1_voting_VotingForum'$1_governance_proposal_GovernanceProposal';
    var $t5: $1_voting_Proposal'$1_governance_proposal_GovernanceProposal';
    var $t6: int;
    var $t7: int;
    var $t8: $Mutation ($1_aptos_governance_ApprovedExecutionHashes);
    var $t9: int;
    var $t10: int;
    var $t11: $1_voting_VotingForum'$1_governance_proposal_GovernanceProposal';
    var $t12: $1_voting_Proposal'$1_governance_proposal_GovernanceProposal';
    var $t13: int;
    var $t14: bool;
    var $t15: bool;
    var $t16: bool;
    var $t17: $1_voting_VotingForum'$1_governance_proposal_GovernanceProposal';
    var $t18: int;
    var $t19: int;
    var $t20: bool;
    var $t21: int;
    var $t22: int;
    var $t23: int;
    var $t24: $1_voting_VotingForum'$1_governance_proposal_GovernanceProposal';
    var $t25: Vec (int);
    var $t26: Table int (Vec (int));
    var $t27: bool;
    var $t28: $Mutation (Table int (Vec (int)));
    var $t29: $Mutation (Vec (int));
    var $t30: $Mutation (Table int (Vec (int)));
    var $t0: int;
    var $temp_0'$1_aptos_governance_ApprovedExecutionHashes': $1_aptos_governance_ApprovedExecutionHashes;
    var $temp_0'u64': int;
    var $temp_0'vec'u8'': Vec (int);
    $t0 := _$t0;

    // bytecode translation starts here
    // assume Identical($t4, global<voting::VotingForum<governance_proposal::GovernanceProposal>>(1)) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.spec.move:368:9+85
    assume {:print "$at(3,20710,20795)"} true;
    assume ($t4 == $ResourceValue($1_voting_VotingForum'$1_governance_proposal_GovernanceProposal'_$memory, 1));

    // assume Identical($t5, table::spec_get<u64, voting::Proposal<governance_proposal::GovernanceProposal>>(select voting::VotingForum.proposals($t4), $t0)) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.spec.move:369:9+68
    assume {:print "$at(3,20804,20872)"} true;
    assume ($t5 == $1_table_spec_get'u64_$1_voting_Proposal'$1_governance_proposal_GovernanceProposal''($proposals#$1_voting_VotingForum'$1_governance_proposal_GovernanceProposal'($t4), $t0));

    // assume Identical($t6, option::spec_borrow<u128>(select voting::Proposal.early_resolution_vote_threshold($t5))) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.spec.move:371:9+95
    assume {:print "$at(3,20959,21054)"} true;
    assume ($t6 == $1_option_spec_borrow'u128'($early_resolution_vote_threshold#$1_voting_Proposal'$1_governance_proposal_GovernanceProposal'($t5)));

    // assume chain_status::$is_operating() at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.spec.move:351:9+38
    assume {:print "$at(3,20149,20187)"} true;
    assume $1_chain_status_$is_operating($1_chain_status_GenesisEndMarker_$memory);

    // trace_local[proposal_id]($t0) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:369:5+1
    assume {:print "$at(2,16182,16183)"} true;
    assume {:print "$track_local(44,0,0):", $t0} $t0 == $t0;

    // $t7 := 0x1 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:370:74+16
    assume {:print "$at(2,16344,16360)"} true;
    $t7 := 1;
    assume $IsValid'address'($t7);

    // $t8 := borrow_global<aptos_governance::ApprovedExecutionHashes>($t7) on_abort goto L7 with $t9 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:370:31+17
    if (!$ResourceExists($1_aptos_governance_ApprovedExecutionHashes_$memory, $t7)) {
        call $ExecFailureAbort();
    } else {
        $t8 := $Mutation($Global($t7), EmptyVec(), $ResourceValue($1_aptos_governance_ApprovedExecutionHashes_$memory, $t7));
    }
    if ($abort_flag) {
        assume {:print "$at(2,16301,16318)"} true;
        $t9 := $abort_code;
        assume {:print "$track_abort(44,0):", $t9} $t9 == $t9;
        goto L7;
    }

    // trace_local[approved_hashes]($t8) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:370:13+15
    $temp_0'$1_aptos_governance_ApprovedExecutionHashes' := $Dereference($t8);
    assume {:print "$track_local(44,0,1):", $temp_0'$1_aptos_governance_ApprovedExecutionHashes'} $temp_0'$1_aptos_governance_ApprovedExecutionHashes' == $temp_0'$1_aptos_governance_ApprovedExecutionHashes';

    // $t10 := 0x1 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:373:77+16
    assume {:print "$at(2,16488,16504)"} true;
    $t10 := 1;
    assume $IsValid'address'($t10);

    // assume Identical($t11, global<voting::VotingForum<governance_proposal::GovernanceProposal>>($t10)) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.spec.move:212:9+75
    assume {:print "$at(154,9952,10027)"} true;
    assume ($t11 == $ResourceValue($1_voting_VotingForum'$1_governance_proposal_GovernanceProposal'_$memory, $t10));

    // assume Identical($t12, table::spec_get<u64, voting::Proposal<governance_proposal::GovernanceProposal>>(select voting::VotingForum.proposals($t11), $t0)) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.spec.move:213:9+68
    assume {:print "$at(154,10036,10104)"} true;
    assume ($t12 == $1_table_spec_get'u64_$1_voting_Proposal'$1_governance_proposal_GovernanceProposal''($proposals#$1_voting_VotingForum'$1_governance_proposal_GovernanceProposal'($t11), $t0));

    // assume Identical($t13, option::spec_borrow<u128>(select voting::Proposal.early_resolution_vote_threshold($t12))) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.spec.move:214:9+95
    assume {:print "$at(154,10113,10208)"} true;
    assume ($t13 == $1_option_spec_borrow'u128'($early_resolution_vote_threshold#$1_voting_Proposal'$1_governance_proposal_GovernanceProposal'($t12)));

    // assume Identical($t14, Gt(timestamp::$now_seconds(), select voting::Proposal.expiration_secs($t12))) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.spec.move:215:9+77
    assume {:print "$at(154,10217,10294)"} true;
    assume ($t14 == ($1_timestamp_$now_seconds($1_timestamp_CurrentTimeMicroseconds_$memory) > $expiration_secs#$1_voting_Proposal'$1_governance_proposal_GovernanceProposal'($t12)));

    // assume Identical($t15, And(option::spec_is_some<u128>(select voting::Proposal.early_resolution_vote_threshold($t12)), Or(Ge(select voting::Proposal.yes_votes($t12), $t13), Ge(select voting::Proposal.no_votes($t12), $t13)))) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.spec.move:216:9+266
    assume {:print "$at(154,10303,10569)"} true;
    assume ($t15 == ($1_option_spec_is_some'u128'($early_resolution_vote_threshold#$1_voting_Proposal'$1_governance_proposal_GovernanceProposal'($t12)) && (($yes_votes#$1_voting_Proposal'$1_governance_proposal_GovernanceProposal'($t12) >= $t13) || ($no_votes#$1_voting_Proposal'$1_governance_proposal_GovernanceProposal'($t12) >= $t13))));

    // assume Identical($t16, Or($t14, $t15)) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.spec.move:219:9+60
    assume {:print "$at(154,10578,10638)"} true;
    assume ($t16 == ($t14 || $t15));

    // assume Identical($t17, global<voting::VotingForum<governance_proposal::GovernanceProposal>>($t10)) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.spec.move:286:9+75
    assume {:print "$at(154,12822,12897)"} true;
    assume ($t17 == $ResourceValue($1_voting_VotingForum'$1_governance_proposal_GovernanceProposal'_$memory, $t10));

    // $t18 := voting::get_proposal_state<governance_proposal::GovernanceProposal>($t10, $t0) on_abort goto L7 with $t9 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:373:30+77
    assume {:print "$at(2,16441,16518)"} true;
    call $t18 := $1_voting_get_proposal_state'$1_governance_proposal_GovernanceProposal'($t10, $t0);
    if ($abort_flag) {
        assume {:print "$at(2,16441,16518)"} true;
        $t9 := $abort_code;
        assume {:print "$track_abort(44,0):", $t9} $t9 == $t9;
        goto L7;
    }

    // $t19 := 1 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:374:35+24
    assume {:print "$at(2,16554,16578)"} true;
    $t19 := 1;
    assume $IsValid'u64'($t19);

    // $t20 := ==($t18, $t19) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:374:32+2
    $t20 := $IsEqual'u64'($t18, $t19);

    // if ($t20) goto L1 else goto L0 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:374:9+106
    if ($t20) { goto L1; } else { goto L0; }

    // label L1 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:374:9+106
L1:

    // goto L2 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:374:9+106
    assume {:print "$at(2,16528,16634)"} true;
    goto L2;

    // label L0 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:374:9+106
L0:

    // destroy($t8) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:374:9+106
    assume {:print "$at(2,16528,16634)"} true;

    // $t21 := 6 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:374:85+28
    $t21 := 6;
    assume $IsValid'u64'($t21);

    // $t22 := error::invalid_argument($t21) on_abort goto L7 with $t9 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:374:61+53
    call $t22 := $1_error_invalid_argument($t21);
    if ($abort_flag) {
        assume {:print "$at(2,16580,16633)"} true;
        $t9 := $abort_code;
        assume {:print "$track_abort(44,0):", $t9} $t9 == $t9;
        goto L7;
    }

    // trace_abort($t22) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:374:9+106
    assume {:print "$at(2,16528,16634)"} true;
    assume {:print "$track_abort(44,0):", $t22} $t22 == $t22;

    // $t9 := move($t22) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:374:9+106
    $t9 := $t22;

    // goto L7 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:374:9+106
    goto L7;

    // label L2 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:376:77+16
    assume {:print "$at(2,16713,16729)"} true;
L2:

    // $t23 := 0x1 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:376:77+16
    assume {:print "$at(2,16713,16729)"} true;
    $t23 := 1;
    assume $IsValid'address'($t23);

    // assume Identical($t24, global<voting::VotingForum<governance_proposal::GovernanceProposal>>($t23)) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.spec.move:286:9+75
    assume {:print "$at(154,12822,12897)"} true;
    assume ($t24 == $ResourceValue($1_voting_VotingForum'$1_governance_proposal_GovernanceProposal'_$memory, $t23));

    // $t25 := voting::get_execution_hash<governance_proposal::GovernanceProposal>($t23, $t0) on_abort goto L7 with $t9 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:376:30+77
    assume {:print "$at(2,16666,16743)"} true;
    call $t25 := $1_voting_get_execution_hash'$1_governance_proposal_GovernanceProposal'($t23, $t0);
    if ($abort_flag) {
        assume {:print "$at(2,16666,16743)"} true;
        $t9 := $abort_code;
        assume {:print "$track_abort(44,0):", $t9} $t9 == $t9;
        goto L7;
    }

    // trace_local[execution_hash]($t25) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:376:13+14
    assume {:print "$track_local(44,0,3):", $t25} $t25 == $t25;

    // $t26 := get_field<aptos_governance::ApprovedExecutionHashes>.hashes($t8) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:380:38+23
    assume {:print "$at(2,16998,17021)"} true;
    $t26 := $hashes#$1_aptos_governance_ApprovedExecutionHashes($Dereference($t8));

    // $t27 := simple_map::contains_key<u64, vector<u8>>($t26, $t0) on_abort goto L7 with $t9 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:380:13+63
    call $t27 := $1_simple_map_contains_key'u64_vec'u8''($t26, $t0);
    if ($abort_flag) {
        assume {:print "$at(2,16973,17036)"} true;
        $t9 := $abort_code;
        assume {:print "$track_abort(44,0):", $t9} $t9 == $t9;
        goto L7;
    }

    // if ($t27) goto L4 else goto L3 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:380:9+346
    if ($t27) { goto L4; } else { goto L3; }

    // label L4 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:381:70+15
    assume {:print "$at(2,17109,17124)"} true;
L4:

    // $t28 := borrow_field<aptos_governance::ApprovedExecutionHashes>.hashes($t8) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:381:65+27
    assume {:print "$at(2,17104,17131)"} true;
    $t28 := $ChildMutation($t8, 0, $hashes#$1_aptos_governance_ApprovedExecutionHashes($Dereference($t8)));

    // $t29 := simple_map::borrow_mut<u64, vector<u8>>($t28, $t0) on_abort goto L7 with $t9 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:381:42+65
    call $t29,$t28 := $1_simple_map_borrow_mut'u64_vec'u8''($t28, $t0);
    if ($abort_flag) {
        assume {:print "$at(2,17081,17146)"} true;
        $t9 := $abort_code;
        assume {:print "$track_abort(44,0):", $t9} $t9 == $t9;
        goto L7;
    }

    // trace_local[current_execution_hash]($t29) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:381:17+22
    $temp_0'vec'u8'' := $Dereference($t29);
    assume {:print "$track_local(44,0,2):", $temp_0'vec'u8''} $temp_0'vec'u8'' == $temp_0'vec'u8'';

    // write_ref($t29, $t25) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:382:13+40
    assume {:print "$at(2,17160,17200)"} true;
    $t29 := $UpdateMutation($t29, $t25);

    // write_back[Reference($t28)[]]($t29) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:382:13+40
    $t28 := $UpdateMutation($t28, UpdateTable($Dereference($t28), ReadVec(p#$Mutation($t29), LenVec(p#$Mutation($t28))), $Dereference($t29)));

    // write_back[Reference($t8).hashes (simple_map::SimpleMap<u64, vector<u8>>)]($t28) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:382:13+40
    $t8 := $UpdateMutation($t8, $Update'$1_aptos_governance_ApprovedExecutionHashes'_hashes($Dereference($t8), $Dereference($t28)));

    // write_back[aptos_governance::ApprovedExecutionHashes@]($t8) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:382:13+40
    $1_aptos_governance_ApprovedExecutionHashes_$memory := $ResourceUpdate($1_aptos_governance_ApprovedExecutionHashes_$memory, $GlobalLocationAddress($t8),
        $Dereference($t8));

    // goto L5 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:380:9+346
    assume {:print "$at(2,16969,17315)"} true;
    goto L5;

    // label L3 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:384:34+15
    assume {:print "$at(2,17252,17267)"} true;
L3:

    // $t30 := borrow_field<aptos_governance::ApprovedExecutionHashes>.hashes($t8) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:384:29+27
    assume {:print "$at(2,17247,17274)"} true;
    $t30 := $ChildMutation($t8, 0, $hashes#$1_aptos_governance_ApprovedExecutionHashes($Dereference($t8)));

    // simple_map::add<u64, vector<u8>>($t30, $t0, $t25) on_abort goto L7 with $t9 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:384:13+73
    call $t30 := $1_simple_map_add'u64_vec'u8''($t30, $t0, $t25);
    if ($abort_flag) {
        assume {:print "$at(2,17231,17304)"} true;
        $t9 := $abort_code;
        assume {:print "$track_abort(44,0):", $t9} $t9 == $t9;
        goto L7;
    }

    // write_back[Reference($t8).hashes (simple_map::SimpleMap<u64, vector<u8>>)]($t30) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:384:13+73
    $t8 := $UpdateMutation($t8, $Update'$1_aptos_governance_ApprovedExecutionHashes'_hashes($Dereference($t8), $Dereference($t30)));

    // write_back[aptos_governance::ApprovedExecutionHashes@]($t8) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:384:13+73
    $1_aptos_governance_ApprovedExecutionHashes_$memory := $ResourceUpdate($1_aptos_governance_ApprovedExecutionHashes_$memory, $GlobalLocationAddress($t8),
        $Dereference($t8));

    // label L5 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:380:9+346
    assume {:print "$at(2,16969,17315)"} true;
L5:

    // label L6 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:386:5+1
    assume {:print "$at(2,17320,17321)"} true;
L6:

    // return () at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:386:5+1
    assume {:print "$at(2,17320,17321)"} true;
    return;

    // label L7 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:386:5+1
L7:

    // abort($t9) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:386:5+1
    assume {:print "$at(2,17320,17321)"} true;
    $abort_code := $t9;
    $abort_flag := true;
    return;

}

// fun aptos_governance::get_signer [baseline] at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:455:5+338
procedure {:inline 1} $1_aptos_governance_get_signer(_$t0: int) returns ($ret0: $signer)
{
    // declare local variables
    var $t1: Table int ($1_account_SignerCapability);
    var $t2: int;
    var $t3: $1_aptos_governance_GovernanceResponsbility;
    var $t4: int;
    var $t5: Table int ($1_account_SignerCapability);
    var $t6: $1_account_SignerCapability;
    var $t7: int;
    var $t8: $signer;
    var $t0: int;
    var $temp_0'address': int;
    var $temp_0'signer': $signer;
    $t0 := _$t0;

    // bytecode translation starts here
    // assume Identical($t1, select aptos_governance::GovernanceResponsbility.signer_caps(global<aptos_governance::GovernanceResponsbility>(1))) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.spec.move:489:9+76
    assume {:print "$at(3,27938,28014)"} true;
    assume ($t1 == $signer_caps#$1_aptos_governance_GovernanceResponsbility($ResourceValue($1_aptos_governance_GovernanceResponsbility_$memory, 1)));

    // trace_local[signer_address]($t0) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:455:5+1
    assume {:print "$at(2,21136,21137)"} true;
    assume {:print "$track_local(44,7,0):", $t0} $t0 == $t0;

    // $t2 := 0x1 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:456:80+16
    assume {:print "$at(2,21298,21314)"} true;
    $t2 := 1;
    assume $IsValid'address'($t2);

    // $t3 := get_global<aptos_governance::GovernanceResponsbility>($t2) on_abort goto L2 with $t4 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:456:41+13
    if (!$ResourceExists($1_aptos_governance_GovernanceResponsbility_$memory, $t2)) {
        call $ExecFailureAbort();
    } else {
        $t3 := $ResourceValue($1_aptos_governance_GovernanceResponsbility_$memory, $t2);
    }
    if ($abort_flag) {
        assume {:print "$at(2,21259,21272)"} true;
        $t4 := $abort_code;
        assume {:print "$track_abort(44,7):", $t4} $t4 == $t4;
        goto L2;
    }

    // $t5 := get_field<aptos_governance::GovernanceResponsbility>.signer_caps($t3) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:457:45+38
    assume {:print "$at(2,21361,21399)"} true;
    $t5 := $signer_caps#$1_aptos_governance_GovernanceResponsbility($t3);

    // $t6 := simple_map::borrow<address, account::SignerCapability>($t5, $t0) on_abort goto L2 with $t4 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:457:26+75
    call $t6 := $1_simple_map_borrow'address_$1_account_SignerCapability'($t5, $t0);
    if ($abort_flag) {
        assume {:print "$at(2,21342,21417)"} true;
        $t4 := $abort_code;
        assume {:print "$track_abort(44,7):", $t4} $t4 == $t4;
        goto L2;
    }

    // assume Identical($t7, select account::SignerCapability.account($t6)) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/account.spec.move:458:9+30
    assume {:print "$at(73,22246,22276)"} true;
    assume ($t7 == $account#$1_account_SignerCapability($t6));

    // $t8 := account::create_signer_with_capability($t6) on_abort goto L2 with $t4 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:458:9+41
    call $t8 := $1_account_create_signer_with_capability($t6);
    if ($abort_flag) {
        assume {:print "$at(2,21427,21468)"} true;
        $t4 := $abort_code;
        assume {:print "$track_abort(44,7):", $t4} $t4 == $t4;
        goto L2;
    }

    // trace_return[0]($t8) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:458:9+41
    assume {:print "$track_return(44,7,0):", $t8} $t8 == $t8;

    // label L1 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:459:5+1
    assume {:print "$at(2,21473,21474)"} true;
L1:

    // return $t8 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:459:5+1
    assume {:print "$at(2,21473,21474)"} true;
    $ret0 := $t8;
    return;

    // label L2 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:459:5+1
L2:

    // abort($t4) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:459:5+1
    assume {:print "$at(2,21473,21474)"} true;
    $abort_code := $t4;
    $abort_flag := true;
    return;

}

// fun aptos_governance::remove_approved_hash [baseline] at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:413:5+517
procedure {:inline 1} $1_aptos_governance_remove_approved_hash(_$t0: int) returns ()
{
    // declare local variables
    var $t1: int;
    var $t2: $Mutation (Table int (Vec (int)));
    var $t3: $1_voting_VotingForum'$1_governance_proposal_GovernanceProposal';
    var $t4: $1_voting_Proposal'$1_governance_proposal_GovernanceProposal';
    var $t5: int;
    var $t6: $1_voting_VotingForum'$1_governance_proposal_GovernanceProposal';
    var $t7: bool;
    var $t8: int;
    var $t9: int;
    var $t10: int;
    var $t11: int;
    var $t12: $Mutation ($1_aptos_governance_ApprovedExecutionHashes);
    var $t13: $Mutation (Table int (Vec (int)));
    var $t14: Table int (Vec (int));
    var $t15: bool;
    var $t16: int;
    var $t17: Vec (int);
    var $t0: int;
    var $temp_0'$1_simple_map_SimpleMap'u64_vec'u8''': Table int (Vec (int));
    var $temp_0'u64': int;
    $t0 := _$t0;

    // bytecode translation starts here
    // assume Identical($t3, global<voting::VotingForum<governance_proposal::GovernanceProposal>>(1)) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.spec.move:427:9+85
    assume {:print "$at(3,24612,24697)"} true;
    assume ($t3 == $ResourceValue($1_voting_VotingForum'$1_governance_proposal_GovernanceProposal'_$memory, 1));

    // assume Identical($t4, table::spec_get<u64, voting::Proposal<governance_proposal::GovernanceProposal>>(select voting::VotingForum.proposals($t3), $t0)) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.spec.move:430:9+68
    assume {:print "$at(3,24870,24938)"} true;
    assume ($t4 == $1_table_spec_get'u64_$1_voting_Proposal'$1_governance_proposal_GovernanceProposal''($proposals#$1_voting_VotingForum'$1_governance_proposal_GovernanceProposal'($t3), $t0));

    // trace_local[proposal_id]($t0) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:413:5+1
    assume {:print "$at(2,18820,18821)"} true;
    assume {:print "$track_local(44,14,0):", $t0} $t0 == $t0;

    // $t5 := 0x1 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:415:53+16
    assume {:print "$at(2,18974,18990)"} true;
    $t5 := 1;
    assume $IsValid'address'($t5);

    // assume Identical($t6, global<voting::VotingForum<governance_proposal::GovernanceProposal>>($t5)) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.spec.move:286:9+75
    assume {:print "$at(154,12822,12897)"} true;
    assume ($t6 == $ResourceValue($1_voting_VotingForum'$1_governance_proposal_GovernanceProposal'_$memory, $t5));

    // $t7 := voting::is_resolved<governance_proposal::GovernanceProposal>($t5, $t0) on_abort goto L7 with $t8 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:415:13+70
    assume {:print "$at(2,18934,19004)"} true;
    call $t7 := $1_voting_is_resolved'$1_governance_proposal_GovernanceProposal'($t5, $t0);
    if ($abort_flag) {
        assume {:print "$at(2,18934,19004)"} true;
        $t8 := $abort_code;
        assume {:print "$track_abort(44,14):", $t8} $t8 == $t8;
        goto L7;
    }

    // if ($t7) goto L1 else goto L0 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:414:9+167
    assume {:print "$at(2,18913,19080)"} true;
    if ($t7) { goto L1; } else { goto L0; }

    // label L1 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:414:9+167
L1:

    // goto L2 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:414:9+167
    assume {:print "$at(2,18913,19080)"} true;
    goto L2;

    // label L0 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:416:37+26
    assume {:print "$at(2,19042,19068)"} true;
L0:

    // $t9 := 8 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:416:37+26
    assume {:print "$at(2,19042,19068)"} true;
    $t9 := 8;
    assume $IsValid'u64'($t9);

    // $t10 := error::invalid_argument($t9) on_abort goto L7 with $t8 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:416:13+51
    call $t10 := $1_error_invalid_argument($t9);
    if ($abort_flag) {
        assume {:print "$at(2,19018,19069)"} true;
        $t8 := $abort_code;
        assume {:print "$track_abort(44,14):", $t8} $t8 == $t8;
        goto L7;
    }

    // trace_abort($t10) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:414:9+167
    assume {:print "$at(2,18913,19080)"} true;
    assume {:print "$track_abort(44,14):", $t10} $t10 == $t10;

    // $t8 := move($t10) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:414:9+167
    $t8 := $t10;

    // goto L7 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:414:9+167
    goto L7;

    // label L2 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:419:79+16
    assume {:print "$at(2,19161,19177)"} true;
L2:

    // $t11 := 0x1 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:419:79+16
    assume {:print "$at(2,19161,19177)"} true;
    $t11 := 1;
    assume $IsValid'address'($t11);

    // $t12 := borrow_global<aptos_governance::ApprovedExecutionHashes>($t11) on_abort goto L7 with $t8 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:419:36+17
    if (!$ResourceExists($1_aptos_governance_ApprovedExecutionHashes_$memory, $t11)) {
        call $ExecFailureAbort();
    } else {
        $t12 := $Mutation($Global($t11), EmptyVec(), $ResourceValue($1_aptos_governance_ApprovedExecutionHashes_$memory, $t11));
    }
    if ($abort_flag) {
        assume {:print "$at(2,19118,19135)"} true;
        $t8 := $abort_code;
        assume {:print "$track_abort(44,14):", $t8} $t8 == $t8;
        goto L7;
    }

    // $t13 := borrow_field<aptos_governance::ApprovedExecutionHashes>.hashes($t12) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:419:31+72
    $t13 := $ChildMutation($t12, 0, $hashes#$1_aptos_governance_ApprovedExecutionHashes($Dereference($t12)));

    // trace_local[approved_hashes]($t13) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:419:13+15
    $temp_0'$1_simple_map_SimpleMap'u64_vec'u8''' := $Dereference($t13);
    assume {:print "$track_local(44,14,2):", $temp_0'$1_simple_map_SimpleMap'u64_vec'u8'''} $temp_0'$1_simple_map_SimpleMap'u64_vec'u8''' == $temp_0'$1_simple_map_SimpleMap'u64_vec'u8''';

    // $t14 := read_ref($t13) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:420:37+31
    assume {:print "$at(2,19223,19254)"} true;
    $t14 := $Dereference($t13);

    // $t15 := simple_map::contains_key<u64, vector<u8>>($t14, $t0) on_abort goto L7 with $t8 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:420:13+55
    call $t15 := $1_simple_map_contains_key'u64_vec'u8''($t14, $t0);
    if ($abort_flag) {
        assume {:print "$at(2,19199,19254)"} true;
        $t8 := $abort_code;
        assume {:print "$track_abort(44,14):", $t8} $t8 == $t8;
        goto L7;
    }

    // if ($t15) goto L4 else goto L8 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:420:9+135
    if ($t15) { goto L4; } else { goto L8; }

    // label L4 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:421:32+15
    assume {:print "$at(2,19289,19304)"} true;
L4:

    // ($t16, $t17) := simple_map::remove<u64, vector<u8>>($t13, $t0) on_abort goto L7 with $t8 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:421:13+49
    assume {:print "$at(2,19270,19319)"} true;
    call $t16,$t17,$t13 := $1_simple_map_remove'u64_vec'u8''($t13, $t0);
    if ($abort_flag) {
        assume {:print "$at(2,19270,19319)"} true;
        $t8 := $abort_code;
        assume {:print "$track_abort(44,14):", $t8} $t8 == $t8;
        goto L7;
    }

    // write_back[Reference($t12).hashes (simple_map::SimpleMap<u64, vector<u8>>)]($t13) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:421:13+49
    $t12 := $UpdateMutation($t12, $Update'$1_aptos_governance_ApprovedExecutionHashes'_hashes($Dereference($t12), $Dereference($t13)));

    // write_back[aptos_governance::ApprovedExecutionHashes@]($t12) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:421:13+49
    $1_aptos_governance_ApprovedExecutionHashes_$memory := $ResourceUpdate($1_aptos_governance_ApprovedExecutionHashes_$memory, $GlobalLocationAddress($t12),
        $Dereference($t12));

    // destroy($t17) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:421:13+49

    // destroy($t16) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:421:13+49

    // goto L5 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:421:62+1
    goto L5;

    // label L3 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:420:9+135
    assume {:print "$at(2,19195,19330)"} true;
L3:

    // destroy($t13) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:420:9+135
    assume {:print "$at(2,19195,19330)"} true;

    // label L5 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:422:10+1
    assume {:print "$at(2,19330,19331)"} true;
L5:

    // label L6 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:423:5+1
    assume {:print "$at(2,19336,19337)"} true;
L6:

    // return () at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:423:5+1
    assume {:print "$at(2,19336,19337)"} true;
    return;

    // label L7 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:423:5+1
L7:

    // abort($t8) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:423:5+1
    assume {:print "$at(2,19336,19337)"} true;
    $abort_code := $t8;
    $abort_flag := true;
    return;

    // label L8 at <internal>:1:1+10
    assume {:print "$at(1,0,10)"} true;
L8:

    // destroy($t12) at <internal>:1:1+10
    assume {:print "$at(1,0,10)"} true;

    // goto L3 at <internal>:1:1+10
    goto L3;

}

// fun aptos_governance::resolve_multi_step_proposal [verification] at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:397:5+881
procedure {:timeLimit 40} $1_aptos_governance_resolve_multi_step_proposal$verify(_$t0: int, _$t1: int, _$t2: Vec (int)) returns ($ret0: $signer)
{
    // declare local variables
    var $t3: $1_voting_VotingForum'$1_governance_proposal_GovernanceProposal';
    var $t4: $1_voting_Proposal'$1_governance_proposal_GovernanceProposal';
    var $t5: $1_string_String;
    var $t6: $1_string_String;
    var $t7: bool;
    var $t8: bool;
    var $t9: Table int (Vec (int));
    var $t10: $1_aptos_governance_GovernanceResponsbility;
    var $t11: $1_account_SignerCapability;
    var $t12: int;
    var $t13: $1_voting_VotingForum'$1_governance_proposal_GovernanceProposal';
    var $t14: $1_voting_Proposal'$1_governance_proposal_GovernanceProposal';
    var $t15: int;
    var $t16: bool;
    var $t17: bool;
    var $t18: bool;
    var $t19: int;
    var $t20: Table int ($1_account_SignerCapability);
    var $t21: int;
    var $t22: $1_voting_VotingForum'$1_governance_proposal_GovernanceProposal';
    var $t23: int;
    var $t24: int;
    var $t25: int;
    var $t26: bool;
    var $t27: $1_voting_VotingForum'$1_governance_proposal_GovernanceProposal';
    var $t28: $1_voting_Proposal'$1_governance_proposal_GovernanceProposal';
    var $t29: $1_voting_VotingForum'$1_governance_proposal_GovernanceProposal';
    var $t30: $1_voting_Proposal'$1_governance_proposal_GovernanceProposal';
    var $t31: int;
    var $t32: Table int ($1_account_SignerCapability);
    var $t33: $signer;
    var $t34: $1_voting_VotingForum'$1_governance_proposal_GovernanceProposal';
    var $t35: $1_voting_Proposal'$1_governance_proposal_GovernanceProposal';
    var $t36: Vec (int);
    var $t37: Table int (Vec (int));
    var $t0: int;
    var $t1: int;
    var $t2: Vec (int);
    var $temp_0'address': int;
    var $temp_0'signer': $signer;
    var $temp_0'u64': int;
    var $temp_0'vec'u8'': Vec (int);
    var $1_voting_VotingForum'$1_governance_proposal_GovernanceProposal'_$memory#27: $Memory $1_voting_VotingForum'$1_governance_proposal_GovernanceProposal';
    var $1_timestamp_CurrentTimeMicroseconds_$memory#28: $Memory $1_timestamp_CurrentTimeMicroseconds;
    var $1_aptos_governance_ApprovedExecutionHashes_$memory#29: $Memory $1_aptos_governance_ApprovedExecutionHashes;
    var $1_aptos_governance_GovernanceResponsbility_$memory#30: $Memory $1_aptos_governance_GovernanceResponsbility;
    $t0 := _$t0;
    $t1 := _$t1;
    $t2 := _$t2;

    // verification entrypoint assumptions
    call $InitVerification();

    // bytecode translation starts here
    // assume WellFormed($t0) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:397:5+1
    assume {:print "$at(2,17872,17873)"} true;
    assume $IsValid'u64'($t0);

    // assume WellFormed($t1) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:397:5+1
    assume $IsValid'address'($t1);

    // assume WellFormed($t2) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:397:5+1
    assume $IsValid'vec'u8''($t2);

    // assume forall $rsc: ResourceDomain<chain_status::GenesisEndMarker>(): WellFormed($rsc) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:397:5+1
    assume (forall $a_0: int :: {$ResourceValue($1_chain_status_GenesisEndMarker_$memory, $a_0)}(var $rsc := $ResourceValue($1_chain_status_GenesisEndMarker_$memory, $a_0);
    ($IsValid'$1_chain_status_GenesisEndMarker'($rsc))));

    // assume forall $rsc: ResourceDomain<timestamp::CurrentTimeMicroseconds>(): WellFormed($rsc) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:397:5+1
    assume (forall $a_0: int :: {$ResourceValue($1_timestamp_CurrentTimeMicroseconds_$memory, $a_0)}(var $rsc := $ResourceValue($1_timestamp_CurrentTimeMicroseconds_$memory, $a_0);
    ($IsValid'$1_timestamp_CurrentTimeMicroseconds'($rsc))));

    // assume forall $rsc: ResourceDomain<voting::VotingForum<governance_proposal::GovernanceProposal>>(): And(WellFormed($rsc), forall $key: select voting::VotingForum.proposals($rsc): And(Le(Len<governance_proposal::GovernanceProposal>(select option::Option.vec(select voting::Proposal.execution_content(table::spec_get<u64, voting::Proposal<governance_proposal::GovernanceProposal>>(select voting::VotingForum.proposals($rsc), $key)))), 1), Le(Len<u128>(select option::Option.vec(select voting::Proposal.early_resolution_vote_threshold(table::spec_get<u64, voting::Proposal<governance_proposal::GovernanceProposal>>(select voting::VotingForum.proposals($rsc), $key)))), 1))) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:397:5+1
    assume (forall $a_0: int :: {$ResourceValue($1_voting_VotingForum'$1_governance_proposal_GovernanceProposal'_$memory, $a_0)}(var $rsc := $ResourceValue($1_voting_VotingForum'$1_governance_proposal_GovernanceProposal'_$memory, $a_0);
    (($IsValid'$1_voting_VotingForum'$1_governance_proposal_GovernanceProposal''($rsc) && (var $range_1 := $proposals#$1_voting_VotingForum'$1_governance_proposal_GovernanceProposal'($rsc); (forall $key: int :: ContainsTable($range_1, $EncodeKey'u64'($key)) ==> (((LenVec($vec#$1_option_Option'$1_governance_proposal_GovernanceProposal'($execution_content#$1_voting_Proposal'$1_governance_proposal_GovernanceProposal'($1_table_spec_get'u64_$1_voting_Proposal'$1_governance_proposal_GovernanceProposal''($proposals#$1_voting_VotingForum'$1_governance_proposal_GovernanceProposal'($rsc), $key)))) <= 1) && (LenVec($vec#$1_option_Option'u128'($early_resolution_vote_threshold#$1_voting_Proposal'$1_governance_proposal_GovernanceProposal'($1_table_spec_get'u64_$1_voting_Proposal'$1_governance_proposal_GovernanceProposal''($proposals#$1_voting_VotingForum'$1_governance_proposal_GovernanceProposal'($rsc), $key)))) <= 1)))))))));

    // assume forall $rsc: ResourceDomain<staking_config::StakingConfig>(): And(WellFormed($rsc), And(And(Le(select staking_config::StakingConfig.rewards_rate($rsc), 1000000), Gt(select staking_config::StakingConfig.rewards_rate_denominator($rsc), 0)), Le(select staking_config::StakingConfig.rewards_rate($rsc), select staking_config::StakingConfig.rewards_rate_denominator($rsc)))) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:397:5+1
    assume (forall $a_0: int :: {$ResourceValue($1_staking_config_StakingConfig_$memory, $a_0)}(var $rsc := $ResourceValue($1_staking_config_StakingConfig_$memory, $a_0);
    (($IsValid'$1_staking_config_StakingConfig'($rsc) && ((($rewards_rate#$1_staking_config_StakingConfig($rsc) <= 1000000) && ($rewards_rate_denominator#$1_staking_config_StakingConfig($rsc) > 0)) && ($rewards_rate#$1_staking_config_StakingConfig($rsc) <= $rewards_rate_denominator#$1_staking_config_StakingConfig($rsc)))))));

    // assume forall $rsc: ResourceDomain<stake::AptosCoinCapabilities>(): WellFormed($rsc) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:397:5+1
    assume (forall $a_0: int :: {$ResourceValue($1_stake_AptosCoinCapabilities_$memory, $a_0)}(var $rsc := $ResourceValue($1_stake_AptosCoinCapabilities_$memory, $a_0);
    ($IsValid'$1_stake_AptosCoinCapabilities'($rsc))));

    // assume forall $rsc: ResourceDomain<stake::ValidatorPerformance>(): WellFormed($rsc) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:397:5+1
    assume (forall $a_0: int :: {$ResourceValue($1_stake_ValidatorPerformance_$memory, $a_0)}(var $rsc := $ResourceValue($1_stake_ValidatorPerformance_$memory, $a_0);
    ($IsValid'$1_stake_ValidatorPerformance'($rsc))));

    // assume forall $rsc: ResourceDomain<stake::ValidatorSet>(): WellFormed($rsc) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:397:5+1
    assume (forall $a_0: int :: {$ResourceValue($1_stake_ValidatorSet_$memory, $a_0)}(var $rsc := $ResourceValue($1_stake_ValidatorSet_$memory, $a_0);
    ($IsValid'$1_stake_ValidatorSet'($rsc))));

    // assume forall $rsc: ResourceDomain<transaction_fee::AptosCoinCapabilities>(): WellFormed($rsc) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:397:5+1
    assume (forall $a_0: int :: {$ResourceValue($1_transaction_fee_AptosCoinCapabilities_$memory, $a_0)}(var $rsc := $ResourceValue($1_transaction_fee_AptosCoinCapabilities_$memory, $a_0);
    ($IsValid'$1_transaction_fee_AptosCoinCapabilities'($rsc))));

    // assume forall $rsc: ResourceDomain<state_storage::GasParameter>(): WellFormed($rsc) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:397:5+1
    assume (forall $a_0: int :: {$ResourceValue($1_state_storage_GasParameter_$memory, $a_0)}(var $rsc := $ResourceValue($1_state_storage_GasParameter_$memory, $a_0);
    ($IsValid'$1_state_storage_GasParameter'($rsc))));

    // assume forall $rsc: ResourceDomain<state_storage::StateStorageUsage>(): WellFormed($rsc) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:397:5+1
    assume (forall $a_0: int :: {$ResourceValue($1_state_storage_StateStorageUsage_$memory, $a_0)}(var $rsc := $ResourceValue($1_state_storage_StateStorageUsage_$memory, $a_0);
    ($IsValid'$1_state_storage_StateStorageUsage'($rsc))));

    // assume forall $rsc: ResourceDomain<storage_gas::StorageGas>(): WellFormed($rsc) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:397:5+1
    assume (forall $a_0: int :: {$ResourceValue($1_storage_gas_StorageGas_$memory, $a_0)}(var $rsc := $ResourceValue($1_storage_gas_StorageGas_$memory, $a_0);
    ($IsValid'$1_storage_gas_StorageGas'($rsc))));

    // assume forall $rsc: ResourceDomain<storage_gas::StorageGasConfig>(): And(WellFormed($rsc), And(And(And(And(And(And(And(And(And(And(And(And(And(And(And(And(And(And(And(And(And(And(And(And(And(And(And(Gt(select storage_gas::UsageGasConfig.target_usage(select storage_gas::StorageGasConfig.item_config($rsc)), 0), Le(select storage_gas::UsageGasConfig.target_usage(select storage_gas::StorageGasConfig.item_config($rsc)), Div(18446744073709551615, 10000))), Le(select storage_gas::GasCurve.min_gas(select storage_gas::UsageGasConfig.read_curve(select storage_gas::StorageGasConfig.item_config($rsc))), select storage_gas::GasCurve.max_gas(select storage_gas::UsageGasConfig.read_curve(select storage_gas::StorageGasConfig.item_config($rsc))))), Le(select storage_gas::GasCurve.max_gas(select storage_gas::UsageGasConfig.read_curve(select storage_gas::StorageGasConfig.item_config($rsc))), Div(18446744073709551615, 10000))), And(And(Implies(Gt(Len<storage_gas::Point>(select storage_gas::GasCurve.points(select storage_gas::UsageGasConfig.read_curve(select storage_gas::StorageGasConfig.item_config($rsc)))), 0), Gt(select storage_gas::Point.x(Index(select storage_gas::GasCurve.points(select storage_gas::UsageGasConfig.read_curve(select storage_gas::StorageGasConfig.item_config($rsc))), 0)), 0)), Implies(Gt(Len<storage_gas::Point>(select storage_gas::GasCurve.points(select storage_gas::UsageGasConfig.read_curve(select storage_gas::StorageGasConfig.item_config($rsc)))), 0), Lt(select storage_gas::Point.x(Index(select storage_gas::GasCurve.points(select storage_gas::UsageGasConfig.read_curve(select storage_gas::StorageGasConfig.item_config($rsc))), Sub(Len<storage_gas::Point>(select storage_gas::GasCurve.points(select storage_gas::UsageGasConfig.read_curve(select storage_gas::StorageGasConfig.item_config($rsc)))), 1))), 10000))), forall i: Range(0, Sub(Len<storage_gas::Point>(select storage_gas::GasCurve.points(select storage_gas::UsageGasConfig.read_curve(select storage_gas::StorageGasConfig.item_config($rsc)))), 1)): And(Lt(select storage_gas::Point.x(Index(select storage_gas::GasCurve.points(select storage_gas::UsageGasConfig.read_curve(select storage_gas::StorageGasConfig.item_config($rsc))), i)), select storage_gas::Point.x(Index(select storage_gas::GasCurve.points(select storage_gas::UsageGasConfig.read_curve(select storage_gas::StorageGasConfig.item_config($rsc))), Add(i, 1)))), Le(select storage_gas::Point.y(Index(select storage_gas::GasCurve.points(select storage_gas::UsageGasConfig.read_curve(select storage_gas::StorageGasConfig.item_config($rsc))), i)), select storage_gas::Point.y(Index(select storage_gas::GasCurve.points(select storage_gas::UsageGasConfig.read_curve(select storage_gas::StorageGasConfig.item_config($rsc))), Add(i, 1))))))), forall $elem: select storage_gas::GasCurve.points(select storage_gas::UsageGasConfig.read_curve(select storage_gas::StorageGasConfig.item_config($rsc))): And(Le(select storage_gas::Point.x($elem), 10000), Le(select storage_gas::Point.y($elem), 10000))), Le(select storage_gas::GasCurve.min_gas(select storage_gas::UsageGasConfig.create_curve(select storage_gas::StorageGasConfig.item_config($rsc))), select storage_gas::GasCurve.max_gas(select storage_gas::UsageGasConfig.create_curve(select storage_gas::StorageGasConfig.item_config($rsc))))), Le(select storage_gas::GasCurve.max_gas(select storage_gas::UsageGasConfig.create_curve(select storage_gas::StorageGasConfig.item_config($rsc))), Div(18446744073709551615, 10000))), And(And(Implies(Gt(Len<storage_gas::Point>(select storage_gas::GasCurve.points(select storage_gas::UsageGasConfig.create_curve(select storage_gas::StorageGasConfig.item_config($rsc)))), 0), Gt(select storage_gas::Point.x(Index(select storage_gas::GasCurve.points(select storage_gas::UsageGasConfig.create_curve(select storage_gas::StorageGasConfig.item_config($rsc))), 0)), 0)), Implies(Gt(Len<storage_gas::Point>(select storage_gas::GasCurve.points(select storage_gas::UsageGasConfig.create_curve(select storage_gas::StorageGasConfig.item_config($rsc)))), 0), Lt(select storage_gas::Point.x(Index(select storage_gas::GasCurve.points(select storage_gas::UsageGasConfig.create_curve(select storage_gas::StorageGasConfig.item_config($rsc))), Sub(Len<storage_gas::Point>(select storage_gas::GasCurve.points(select storage_gas::UsageGasConfig.create_curve(select storage_gas::StorageGasConfig.item_config($rsc)))), 1))), 10000))), forall i: Range(0, Sub(Len<storage_gas::Point>(select storage_gas::GasCurve.points(select storage_gas::UsageGasConfig.create_curve(select storage_gas::StorageGasConfig.item_config($rsc)))), 1)): And(Lt(select storage_gas::Point.x(Index(select storage_gas::GasCurve.points(select storage_gas::UsageGasConfig.create_curve(select storage_gas::StorageGasConfig.item_config($rsc))), i)), select storage_gas::Point.x(Index(select storage_gas::GasCurve.points(select storage_gas::UsageGasConfig.create_curve(select storage_gas::StorageGasConfig.item_config($rsc))), Add(i, 1)))), Le(select storage_gas::Point.y(Index(select storage_gas::GasCurve.points(select storage_gas::UsageGasConfig.create_curve(select storage_gas::StorageGasConfig.item_config($rsc))), i)), select storage_gas::Point.y(Index(select storage_gas::GasCurve.points(select storage_gas::UsageGasConfig.create_curve(select storage_gas::StorageGasConfig.item_config($rsc))), Add(i, 1))))))), forall $elem: select storage_gas::GasCurve.points(select storage_gas::UsageGasConfig.create_curve(select storage_gas::StorageGasConfig.item_config($rsc))): And(Le(select storage_gas::Point.x($elem), 10000), Le(select storage_gas::Point.y($elem), 10000))), Le(select storage_gas::GasCurve.min_gas(select storage_gas::UsageGasConfig.write_curve(select storage_gas::StorageGasConfig.item_config($rsc))), select storage_gas::GasCurve.max_gas(select storage_gas::UsageGasConfig.write_curve(select storage_gas::StorageGasConfig.item_config($rsc))))), Le(select storage_gas::GasCurve.max_gas(select storage_gas::UsageGasConfig.write_curve(select storage_gas::StorageGasConfig.item_config($rsc))), Div(18446744073709551615, 10000))), And(And(Implies(Gt(Len<storage_gas::Point>(select storage_gas::GasCurve.points(select storage_gas::UsageGasConfig.write_curve(select storage_gas::StorageGasConfig.item_config($rsc)))), 0), Gt(select storage_gas::Point.x(Index(select storage_gas::GasCurve.points(select storage_gas::UsageGasConfig.write_curve(select storage_gas::StorageGasConfig.item_config($rsc))), 0)), 0)), Implies(Gt(Len<storage_gas::Point>(select storage_gas::GasCurve.points(select storage_gas::UsageGasConfig.write_curve(select storage_gas::StorageGasConfig.item_config($rsc)))), 0), Lt(select storage_gas::Point.x(Index(select storage_gas::GasCurve.points(select storage_gas::UsageGasConfig.write_curve(select storage_gas::StorageGasConfig.item_config($rsc))), Sub(Len<storage_gas::Point>(select storage_gas::GasCurve.points(select storage_gas::UsageGasConfig.write_curve(select storage_gas::StorageGasConfig.item_config($rsc)))), 1))), 10000))), forall i: Range(0, Sub(Len<storage_gas::Point>(select storage_gas::GasCurve.points(select storage_gas::UsageGasConfig.write_curve(select storage_gas::StorageGasConfig.item_config($rsc)))), 1)): And(Lt(select storage_gas::Point.x(Index(select storage_gas::GasCurve.points(select storage_gas::UsageGasConfig.write_curve(select storage_gas::StorageGasConfig.item_config($rsc))), i)), select storage_gas::Point.x(Index(select storage_gas::GasCurve.points(select storage_gas::UsageGasConfig.write_curve(select storage_gas::StorageGasConfig.item_config($rsc))), Add(i, 1)))), Le(select storage_gas::Point.y(Index(select storage_gas::GasCurve.points(select storage_gas::UsageGasConfig.write_curve(select storage_gas::StorageGasConfig.item_config($rsc))), i)), select storage_gas::Point.y(Index(select storage_gas::GasCurve.points(select storage_gas::UsageGasConfig.write_curve(select storage_gas::StorageGasConfig.item_config($rsc))), Add(i, 1))))))), forall $elem: select storage_gas::GasCurve.points(select storage_gas::UsageGasConfig.write_curve(select storage_gas::StorageGasConfig.item_config($rsc))): And(Le(select storage_gas::Point.x($elem), 10000), Le(select storage_gas::Point.y($elem), 10000))), Gt(select storage_gas::UsageGasConfig.target_usage(select storage_gas::StorageGasConfig.byte_config($rsc)), 0)), Le(select storage_gas::UsageGasConfig.target_usage(select storage_gas::StorageGasConfig.byte_config($rsc)), Div(18446744073709551615, 10000))), Le(select storage_gas::GasCurve.min_gas(select storage_gas::UsageGasConfig.read_curve(select storage_gas::StorageGasConfig.byte_config($rsc))), select storage_gas::GasCurve.max_gas(select storage_gas::UsageGasConfig.read_curve(select storage_gas::StorageGasConfig.byte_config($rsc))))), Le(select storage_gas::GasCurve.max_gas(select storage_gas::UsageGasConfig.read_curve(select storage_gas::StorageGasConfig.byte_config($rsc))), Div(18446744073709551615, 10000))), And(And(Implies(Gt(Len<storage_gas::Point>(select storage_gas::GasCurve.points(select storage_gas::UsageGasConfig.read_curve(select storage_gas::StorageGasConfig.byte_config($rsc)))), 0), Gt(select storage_gas::Point.x(Index(select storage_gas::GasCurve.points(select storage_gas::UsageGasConfig.read_curve(select storage_gas::StorageGasConfig.byte_config($rsc))), 0)), 0)), Implies(Gt(Len<storage_gas::Point>(select storage_gas::GasCurve.points(select storage_gas::UsageGasConfig.read_curve(select storage_gas::StorageGasConfig.byte_config($rsc)))), 0), Lt(select storage_gas::Point.x(Index(select storage_gas::GasCurve.points(select storage_gas::UsageGasConfig.read_curve(select storage_gas::StorageGasConfig.byte_config($rsc))), Sub(Len<storage_gas::Point>(select storage_gas::GasCurve.points(select storage_gas::UsageGasConfig.read_curve(select storage_gas::StorageGasConfig.byte_config($rsc)))), 1))), 10000))), forall i: Range(0, Sub(Len<storage_gas::Point>(select storage_gas::GasCurve.points(select storage_gas::UsageGasConfig.read_curve(select storage_gas::StorageGasConfig.byte_config($rsc)))), 1)): And(Lt(select storage_gas::Point.x(Index(select storage_gas::GasCurve.points(select storage_gas::UsageGasConfig.read_curve(select storage_gas::StorageGasConfig.byte_config($rsc))), i)), select storage_gas::Point.x(Index(select storage_gas::GasCurve.points(select storage_gas::UsageGasConfig.read_curve(select storage_gas::StorageGasConfig.byte_config($rsc))), Add(i, 1)))), Le(select storage_gas::Point.y(Index(select storage_gas::GasCurve.points(select storage_gas::UsageGasConfig.read_curve(select storage_gas::StorageGasConfig.byte_config($rsc))), i)), select storage_gas::Point.y(Index(select storage_gas::GasCurve.points(select storage_gas::UsageGasConfig.read_curve(select storage_gas::StorageGasConfig.byte_config($rsc))), Add(i, 1))))))), forall $elem: select storage_gas::GasCurve.points(select storage_gas::UsageGasConfig.read_curve(select storage_gas::StorageGasConfig.byte_config($rsc))): And(Le(select storage_gas::Point.x($elem), 10000), Le(select storage_gas::Point.y($elem), 10000))), Le(select storage_gas::GasCurve.min_gas(select storage_gas::UsageGasConfig.create_curve(select storage_gas::StorageGasConfig.byte_config($rsc))), select storage_gas::GasCurve.max_gas(select storage_gas::UsageGasConfig.create_curve(select storage_gas::StorageGasConfig.byte_config($rsc))))), Le(select storage_gas::GasCurve.max_gas(select storage_gas::UsageGasConfig.create_curve(select storage_gas::StorageGasConfig.byte_config($rsc))), Div(18446744073709551615, 10000))), And(And(Implies(Gt(Len<storage_gas::Point>(select storage_gas::GasCurve.points(select storage_gas::UsageGasConfig.create_curve(select storage_gas::StorageGasConfig.byte_config($rsc)))), 0), Gt(select storage_gas::Point.x(Index(select storage_gas::GasCurve.points(select storage_gas::UsageGasConfig.create_curve(select storage_gas::StorageGasConfig.byte_config($rsc))), 0)), 0)), Implies(Gt(Len<storage_gas::Point>(select storage_gas::GasCurve.points(select storage_gas::UsageGasConfig.create_curve(select storage_gas::StorageGasConfig.byte_config($rsc)))), 0), Lt(select storage_gas::Point.x(Index(select storage_gas::GasCurve.points(select storage_gas::UsageGasConfig.create_curve(select storage_gas::StorageGasConfig.byte_config($rsc))), Sub(Len<storage_gas::Point>(select storage_gas::GasCurve.points(select storage_gas::UsageGasConfig.create_curve(select storage_gas::StorageGasConfig.byte_config($rsc)))), 1))), 10000))), forall i: Range(0, Sub(Len<storage_gas::Point>(select storage_gas::GasCurve.points(select storage_gas::UsageGasConfig.create_curve(select storage_gas::StorageGasConfig.byte_config($rsc)))), 1)): And(Lt(select storage_gas::Point.x(Index(select storage_gas::GasCurve.points(select storage_gas::UsageGasConfig.create_curve(select storage_gas::StorageGasConfig.byte_config($rsc))), i)), select storage_gas::Point.x(Index(select storage_gas::GasCurve.points(select storage_gas::UsageGasConfig.create_curve(select storage_gas::StorageGasConfig.byte_config($rsc))), Add(i, 1)))), Le(select storage_gas::Point.y(Index(select storage_gas::GasCurve.points(select storage_gas::UsageGasConfig.create_curve(select storage_gas::StorageGasConfig.byte_config($rsc))), i)), select storage_gas::Point.y(Index(select storage_gas::GasCurve.points(select storage_gas::UsageGasConfig.create_curve(select storage_gas::StorageGasConfig.byte_config($rsc))), Add(i, 1))))))), forall $elem: select storage_gas::GasCurve.points(select storage_gas::UsageGasConfig.create_curve(select storage_gas::StorageGasConfig.byte_config($rsc))): And(Le(select storage_gas::Point.x($elem), 10000), Le(select storage_gas::Point.y($elem), 10000))), Le(select storage_gas::GasCurve.min_gas(select storage_gas::UsageGasConfig.write_curve(select storage_gas::StorageGasConfig.byte_config($rsc))), select storage_gas::GasCurve.max_gas(select storage_gas::UsageGasConfig.write_curve(select storage_gas::StorageGasConfig.byte_config($rsc))))), Le(select storage_gas::GasCurve.max_gas(select storage_gas::UsageGasConfig.write_curve(select storage_gas::StorageGasConfig.byte_config($rsc))), Div(18446744073709551615, 10000))), And(And(Implies(Gt(Len<storage_gas::Point>(select storage_gas::GasCurve.points(select storage_gas::UsageGasConfig.write_curve(select storage_gas::StorageGasConfig.byte_config($rsc)))), 0), Gt(select storage_gas::Point.x(Index(select storage_gas::GasCurve.points(select storage_gas::UsageGasConfig.write_curve(select storage_gas::StorageGasConfig.byte_config($rsc))), 0)), 0)), Implies(Gt(Len<storage_gas::Point>(select storage_gas::GasCurve.points(select storage_gas::UsageGasConfig.write_curve(select storage_gas::StorageGasConfig.byte_config($rsc)))), 0), Lt(select storage_gas::Point.x(Index(select storage_gas::GasCurve.points(select storage_gas::UsageGasConfig.write_curve(select storage_gas::StorageGasConfig.byte_config($rsc))), Sub(Len<storage_gas::Point>(select storage_gas::GasCurve.points(select storage_gas::UsageGasConfig.write_curve(select storage_gas::StorageGasConfig.byte_config($rsc)))), 1))), 10000))), forall i: Range(0, Sub(Len<storage_gas::Point>(select storage_gas::GasCurve.points(select storage_gas::UsageGasConfig.write_curve(select storage_gas::StorageGasConfig.byte_config($rsc)))), 1)): And(Lt(select storage_gas::Point.x(Index(select storage_gas::GasCurve.points(select storage_gas::UsageGasConfig.write_curve(select storage_gas::StorageGasConfig.byte_config($rsc))), i)), select storage_gas::Point.x(Index(select storage_gas::GasCurve.points(select storage_gas::UsageGasConfig.write_curve(select storage_gas::StorageGasConfig.byte_config($rsc))), Add(i, 1)))), Le(select storage_gas::Point.y(Index(select storage_gas::GasCurve.points(select storage_gas::UsageGasConfig.write_curve(select storage_gas::StorageGasConfig.byte_config($rsc))), i)), select storage_gas::Point.y(Index(select storage_gas::GasCurve.points(select storage_gas::UsageGasConfig.write_curve(select storage_gas::StorageGasConfig.byte_config($rsc))), Add(i, 1))))))), forall $elem: select storage_gas::GasCurve.points(select storage_gas::UsageGasConfig.write_curve(select storage_gas::StorageGasConfig.byte_config($rsc))): And(Le(select storage_gas::Point.x($elem), 10000), Le(select storage_gas::Point.y($elem), 10000)))) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:397:5+1
    assume (forall $a_0: int :: {$ResourceValue($1_storage_gas_StorageGasConfig_$memory, $a_0)}(var $rsc := $ResourceValue($1_storage_gas_StorageGasConfig_$memory, $a_0);
    (($IsValid'$1_storage_gas_StorageGasConfig'($rsc) && (((((((((((((((((((((((((((($target_usage#$1_storage_gas_UsageGasConfig($item_config#$1_storage_gas_StorageGasConfig($rsc)) > 0) && ($target_usage#$1_storage_gas_UsageGasConfig($item_config#$1_storage_gas_StorageGasConfig($rsc)) <= (18446744073709551615 div 10000))) && ($min_gas#$1_storage_gas_GasCurve($read_curve#$1_storage_gas_UsageGasConfig($item_config#$1_storage_gas_StorageGasConfig($rsc))) <= $max_gas#$1_storage_gas_GasCurve($read_curve#$1_storage_gas_UsageGasConfig($item_config#$1_storage_gas_StorageGasConfig($rsc))))) && ($max_gas#$1_storage_gas_GasCurve($read_curve#$1_storage_gas_UsageGasConfig($item_config#$1_storage_gas_StorageGasConfig($rsc))) <= (18446744073709551615 div 10000))) && ((((LenVec($points#$1_storage_gas_GasCurve($read_curve#$1_storage_gas_UsageGasConfig($item_config#$1_storage_gas_StorageGasConfig($rsc)))) > 0) ==> ($x#$1_storage_gas_Point(ReadVec($points#$1_storage_gas_GasCurve($read_curve#$1_storage_gas_UsageGasConfig($item_config#$1_storage_gas_StorageGasConfig($rsc))), 0)) > 0)) && ((LenVec($points#$1_storage_gas_GasCurve($read_curve#$1_storage_gas_UsageGasConfig($item_config#$1_storage_gas_StorageGasConfig($rsc)))) > 0) ==> ($x#$1_storage_gas_Point(ReadVec($points#$1_storage_gas_GasCurve($read_curve#$1_storage_gas_UsageGasConfig($item_config#$1_storage_gas_StorageGasConfig($rsc))), (LenVec($points#$1_storage_gas_GasCurve($read_curve#$1_storage_gas_UsageGasConfig($item_config#$1_storage_gas_StorageGasConfig($rsc)))) - 1))) < 10000))) && (var $range_1 := $Range(0, (LenVec($points#$1_storage_gas_GasCurve($read_curve#$1_storage_gas_UsageGasConfig($item_config#$1_storage_gas_StorageGasConfig($rsc)))) - 1)); (forall $i_2: int :: $InRange($range_1, $i_2) ==> (var i := $i_2;
    ((($x#$1_storage_gas_Point(ReadVec($points#$1_storage_gas_GasCurve($read_curve#$1_storage_gas_UsageGasConfig($item_config#$1_storage_gas_StorageGasConfig($rsc))), i)) < $x#$1_storage_gas_Point(ReadVec($points#$1_storage_gas_GasCurve($read_curve#$1_storage_gas_UsageGasConfig($item_config#$1_storage_gas_StorageGasConfig($rsc))), (i + 1)))) && ($y#$1_storage_gas_Point(ReadVec($points#$1_storage_gas_GasCurve($read_curve#$1_storage_gas_UsageGasConfig($item_config#$1_storage_gas_StorageGasConfig($rsc))), i)) <= $y#$1_storage_gas_Point(ReadVec($points#$1_storage_gas_GasCurve($read_curve#$1_storage_gas_UsageGasConfig($item_config#$1_storage_gas_StorageGasConfig($rsc))), (i + 1))))))))))) && (var $range_3 := $points#$1_storage_gas_GasCurve($read_curve#$1_storage_gas_UsageGasConfig($item_config#$1_storage_gas_StorageGasConfig($rsc))); (forall $i_4: int :: InRangeVec($range_3, $i_4) ==> (var $elem := ReadVec($range_3, $i_4);
    ((($x#$1_storage_gas_Point($elem) <= 10000) && ($y#$1_storage_gas_Point($elem) <= 10000))))))) && ($min_gas#$1_storage_gas_GasCurve($create_curve#$1_storage_gas_UsageGasConfig($item_config#$1_storage_gas_StorageGasConfig($rsc))) <= $max_gas#$1_storage_gas_GasCurve($create_curve#$1_storage_gas_UsageGasConfig($item_config#$1_storage_gas_StorageGasConfig($rsc))))) && ($max_gas#$1_storage_gas_GasCurve($create_curve#$1_storage_gas_UsageGasConfig($item_config#$1_storage_gas_StorageGasConfig($rsc))) <= (18446744073709551615 div 10000))) && ((((LenVec($points#$1_storage_gas_GasCurve($create_curve#$1_storage_gas_UsageGasConfig($item_config#$1_storage_gas_StorageGasConfig($rsc)))) > 0) ==> ($x#$1_storage_gas_Point(ReadVec($points#$1_storage_gas_GasCurve($create_curve#$1_storage_gas_UsageGasConfig($item_config#$1_storage_gas_StorageGasConfig($rsc))), 0)) > 0)) && ((LenVec($points#$1_storage_gas_GasCurve($create_curve#$1_storage_gas_UsageGasConfig($item_config#$1_storage_gas_StorageGasConfig($rsc)))) > 0) ==> ($x#$1_storage_gas_Point(ReadVec($points#$1_storage_gas_GasCurve($create_curve#$1_storage_gas_UsageGasConfig($item_config#$1_storage_gas_StorageGasConfig($rsc))), (LenVec($points#$1_storage_gas_GasCurve($create_curve#$1_storage_gas_UsageGasConfig($item_config#$1_storage_gas_StorageGasConfig($rsc)))) - 1))) < 10000))) && (var $range_5 := $Range(0, (LenVec($points#$1_storage_gas_GasCurve($create_curve#$1_storage_gas_UsageGasConfig($item_config#$1_storage_gas_StorageGasConfig($rsc)))) - 1)); (forall $i_6: int :: $InRange($range_5, $i_6) ==> (var i := $i_6;
    ((($x#$1_storage_gas_Point(ReadVec($points#$1_storage_gas_GasCurve($create_curve#$1_storage_gas_UsageGasConfig($item_config#$1_storage_gas_StorageGasConfig($rsc))), i)) < $x#$1_storage_gas_Point(ReadVec($points#$1_storage_gas_GasCurve($create_curve#$1_storage_gas_UsageGasConfig($item_config#$1_storage_gas_StorageGasConfig($rsc))), (i + 1)))) && ($y#$1_storage_gas_Point(ReadVec($points#$1_storage_gas_GasCurve($create_curve#$1_storage_gas_UsageGasConfig($item_config#$1_storage_gas_StorageGasConfig($rsc))), i)) <= $y#$1_storage_gas_Point(ReadVec($points#$1_storage_gas_GasCurve($create_curve#$1_storage_gas_UsageGasConfig($item_config#$1_storage_gas_StorageGasConfig($rsc))), (i + 1))))))))))) && (var $range_7 := $points#$1_storage_gas_GasCurve($create_curve#$1_storage_gas_UsageGasConfig($item_config#$1_storage_gas_StorageGasConfig($rsc))); (forall $i_8: int :: InRangeVec($range_7, $i_8) ==> (var $elem := ReadVec($range_7, $i_8);
    ((($x#$1_storage_gas_Point($elem) <= 10000) && ($y#$1_storage_gas_Point($elem) <= 10000))))))) && ($min_gas#$1_storage_gas_GasCurve($write_curve#$1_storage_gas_UsageGasConfig($item_config#$1_storage_gas_StorageGasConfig($rsc))) <= $max_gas#$1_storage_gas_GasCurve($write_curve#$1_storage_gas_UsageGasConfig($item_config#$1_storage_gas_StorageGasConfig($rsc))))) && ($max_gas#$1_storage_gas_GasCurve($write_curve#$1_storage_gas_UsageGasConfig($item_config#$1_storage_gas_StorageGasConfig($rsc))) <= (18446744073709551615 div 10000))) && ((((LenVec($points#$1_storage_gas_GasCurve($write_curve#$1_storage_gas_UsageGasConfig($item_config#$1_storage_gas_StorageGasConfig($rsc)))) > 0) ==> ($x#$1_storage_gas_Point(ReadVec($points#$1_storage_gas_GasCurve($write_curve#$1_storage_gas_UsageGasConfig($item_config#$1_storage_gas_StorageGasConfig($rsc))), 0)) > 0)) && ((LenVec($points#$1_storage_gas_GasCurve($write_curve#$1_storage_gas_UsageGasConfig($item_config#$1_storage_gas_StorageGasConfig($rsc)))) > 0) ==> ($x#$1_storage_gas_Point(ReadVec($points#$1_storage_gas_GasCurve($write_curve#$1_storage_gas_UsageGasConfig($item_config#$1_storage_gas_StorageGasConfig($rsc))), (LenVec($points#$1_storage_gas_GasCurve($write_curve#$1_storage_gas_UsageGasConfig($item_config#$1_storage_gas_StorageGasConfig($rsc)))) - 1))) < 10000))) && (var $range_9 := $Range(0, (LenVec($points#$1_storage_gas_GasCurve($write_curve#$1_storage_gas_UsageGasConfig($item_config#$1_storage_gas_StorageGasConfig($rsc)))) - 1)); (forall $i_10: int :: $InRange($range_9, $i_10) ==> (var i := $i_10;
    ((($x#$1_storage_gas_Point(ReadVec($points#$1_storage_gas_GasCurve($write_curve#$1_storage_gas_UsageGasConfig($item_config#$1_storage_gas_StorageGasConfig($rsc))), i)) < $x#$1_storage_gas_Point(ReadVec($points#$1_storage_gas_GasCurve($write_curve#$1_storage_gas_UsageGasConfig($item_config#$1_storage_gas_StorageGasConfig($rsc))), (i + 1)))) && ($y#$1_storage_gas_Point(ReadVec($points#$1_storage_gas_GasCurve($write_curve#$1_storage_gas_UsageGasConfig($item_config#$1_storage_gas_StorageGasConfig($rsc))), i)) <= $y#$1_storage_gas_Point(ReadVec($points#$1_storage_gas_GasCurve($write_curve#$1_storage_gas_UsageGasConfig($item_config#$1_storage_gas_StorageGasConfig($rsc))), (i + 1))))))))))) && (var $range_11 := $points#$1_storage_gas_GasCurve($write_curve#$1_storage_gas_UsageGasConfig($item_config#$1_storage_gas_StorageGasConfig($rsc))); (forall $i_12: int :: InRangeVec($range_11, $i_12) ==> (var $elem := ReadVec($range_11, $i_12);
    ((($x#$1_storage_gas_Point($elem) <= 10000) && ($y#$1_storage_gas_Point($elem) <= 10000))))))) && ($target_usage#$1_storage_gas_UsageGasConfig($byte_config#$1_storage_gas_StorageGasConfig($rsc)) > 0)) && ($target_usage#$1_storage_gas_UsageGasConfig($byte_config#$1_storage_gas_StorageGasConfig($rsc)) <= (18446744073709551615 div 10000))) && ($min_gas#$1_storage_gas_GasCurve($read_curve#$1_storage_gas_UsageGasConfig($byte_config#$1_storage_gas_StorageGasConfig($rsc))) <= $max_gas#$1_storage_gas_GasCurve($read_curve#$1_storage_gas_UsageGasConfig($byte_config#$1_storage_gas_StorageGasConfig($rsc))))) && ($max_gas#$1_storage_gas_GasCurve($read_curve#$1_storage_gas_UsageGasConfig($byte_config#$1_storage_gas_StorageGasConfig($rsc))) <= (18446744073709551615 div 10000))) && ((((LenVec($points#$1_storage_gas_GasCurve($read_curve#$1_storage_gas_UsageGasConfig($byte_config#$1_storage_gas_StorageGasConfig($rsc)))) > 0) ==> ($x#$1_storage_gas_Point(ReadVec($points#$1_storage_gas_GasCurve($read_curve#$1_storage_gas_UsageGasConfig($byte_config#$1_storage_gas_StorageGasConfig($rsc))), 0)) > 0)) && ((LenVec($points#$1_storage_gas_GasCurve($read_curve#$1_storage_gas_UsageGasConfig($byte_config#$1_storage_gas_StorageGasConfig($rsc)))) > 0) ==> ($x#$1_storage_gas_Point(ReadVec($points#$1_storage_gas_GasCurve($read_curve#$1_storage_gas_UsageGasConfig($byte_config#$1_storage_gas_StorageGasConfig($rsc))), (LenVec($points#$1_storage_gas_GasCurve($read_curve#$1_storage_gas_UsageGasConfig($byte_config#$1_storage_gas_StorageGasConfig($rsc)))) - 1))) < 10000))) && (var $range_13 := $Range(0, (LenVec($points#$1_storage_gas_GasCurve($read_curve#$1_storage_gas_UsageGasConfig($byte_config#$1_storage_gas_StorageGasConfig($rsc)))) - 1)); (forall $i_14: int :: $InRange($range_13, $i_14) ==> (var i := $i_14;
    ((($x#$1_storage_gas_Point(ReadVec($points#$1_storage_gas_GasCurve($read_curve#$1_storage_gas_UsageGasConfig($byte_config#$1_storage_gas_StorageGasConfig($rsc))), i)) < $x#$1_storage_gas_Point(ReadVec($points#$1_storage_gas_GasCurve($read_curve#$1_storage_gas_UsageGasConfig($byte_config#$1_storage_gas_StorageGasConfig($rsc))), (i + 1)))) && ($y#$1_storage_gas_Point(ReadVec($points#$1_storage_gas_GasCurve($read_curve#$1_storage_gas_UsageGasConfig($byte_config#$1_storage_gas_StorageGasConfig($rsc))), i)) <= $y#$1_storage_gas_Point(ReadVec($points#$1_storage_gas_GasCurve($read_curve#$1_storage_gas_UsageGasConfig($byte_config#$1_storage_gas_StorageGasConfig($rsc))), (i + 1))))))))))) && (var $range_15 := $points#$1_storage_gas_GasCurve($read_curve#$1_storage_gas_UsageGasConfig($byte_config#$1_storage_gas_StorageGasConfig($rsc))); (forall $i_16: int :: InRangeVec($range_15, $i_16) ==> (var $elem := ReadVec($range_15, $i_16);
    ((($x#$1_storage_gas_Point($elem) <= 10000) && ($y#$1_storage_gas_Point($elem) <= 10000))))))) && ($min_gas#$1_storage_gas_GasCurve($create_curve#$1_storage_gas_UsageGasConfig($byte_config#$1_storage_gas_StorageGasConfig($rsc))) <= $max_gas#$1_storage_gas_GasCurve($create_curve#$1_storage_gas_UsageGasConfig($byte_config#$1_storage_gas_StorageGasConfig($rsc))))) && ($max_gas#$1_storage_gas_GasCurve($create_curve#$1_storage_gas_UsageGasConfig($byte_config#$1_storage_gas_StorageGasConfig($rsc))) <= (18446744073709551615 div 10000))) && ((((LenVec($points#$1_storage_gas_GasCurve($create_curve#$1_storage_gas_UsageGasConfig($byte_config#$1_storage_gas_StorageGasConfig($rsc)))) > 0) ==> ($x#$1_storage_gas_Point(ReadVec($points#$1_storage_gas_GasCurve($create_curve#$1_storage_gas_UsageGasConfig($byte_config#$1_storage_gas_StorageGasConfig($rsc))), 0)) > 0)) && ((LenVec($points#$1_storage_gas_GasCurve($create_curve#$1_storage_gas_UsageGasConfig($byte_config#$1_storage_gas_StorageGasConfig($rsc)))) > 0) ==> ($x#$1_storage_gas_Point(ReadVec($points#$1_storage_gas_GasCurve($create_curve#$1_storage_gas_UsageGasConfig($byte_config#$1_storage_gas_StorageGasConfig($rsc))), (LenVec($points#$1_storage_gas_GasCurve($create_curve#$1_storage_gas_UsageGasConfig($byte_config#$1_storage_gas_StorageGasConfig($rsc)))) - 1))) < 10000))) && (var $range_17 := $Range(0, (LenVec($points#$1_storage_gas_GasCurve($create_curve#$1_storage_gas_UsageGasConfig($byte_config#$1_storage_gas_StorageGasConfig($rsc)))) - 1)); (forall $i_18: int :: $InRange($range_17, $i_18) ==> (var i := $i_18;
    ((($x#$1_storage_gas_Point(ReadVec($points#$1_storage_gas_GasCurve($create_curve#$1_storage_gas_UsageGasConfig($byte_config#$1_storage_gas_StorageGasConfig($rsc))), i)) < $x#$1_storage_gas_Point(ReadVec($points#$1_storage_gas_GasCurve($create_curve#$1_storage_gas_UsageGasConfig($byte_config#$1_storage_gas_StorageGasConfig($rsc))), (i + 1)))) && ($y#$1_storage_gas_Point(ReadVec($points#$1_storage_gas_GasCurve($create_curve#$1_storage_gas_UsageGasConfig($byte_config#$1_storage_gas_StorageGasConfig($rsc))), i)) <= $y#$1_storage_gas_Point(ReadVec($points#$1_storage_gas_GasCurve($create_curve#$1_storage_gas_UsageGasConfig($byte_config#$1_storage_gas_StorageGasConfig($rsc))), (i + 1))))))))))) && (var $range_19 := $points#$1_storage_gas_GasCurve($create_curve#$1_storage_gas_UsageGasConfig($byte_config#$1_storage_gas_StorageGasConfig($rsc))); (forall $i_20: int :: InRangeVec($range_19, $i_20) ==> (var $elem := ReadVec($range_19, $i_20);
    ((($x#$1_storage_gas_Point($elem) <= 10000) && ($y#$1_storage_gas_Point($elem) <= 10000))))))) && ($min_gas#$1_storage_gas_GasCurve($write_curve#$1_storage_gas_UsageGasConfig($byte_config#$1_storage_gas_StorageGasConfig($rsc))) <= $max_gas#$1_storage_gas_GasCurve($write_curve#$1_storage_gas_UsageGasConfig($byte_config#$1_storage_gas_StorageGasConfig($rsc))))) && ($max_gas#$1_storage_gas_GasCurve($write_curve#$1_storage_gas_UsageGasConfig($byte_config#$1_storage_gas_StorageGasConfig($rsc))) <= (18446744073709551615 div 10000))) && ((((LenVec($points#$1_storage_gas_GasCurve($write_curve#$1_storage_gas_UsageGasConfig($byte_config#$1_storage_gas_StorageGasConfig($rsc)))) > 0) ==> ($x#$1_storage_gas_Point(ReadVec($points#$1_storage_gas_GasCurve($write_curve#$1_storage_gas_UsageGasConfig($byte_config#$1_storage_gas_StorageGasConfig($rsc))), 0)) > 0)) && ((LenVec($points#$1_storage_gas_GasCurve($write_curve#$1_storage_gas_UsageGasConfig($byte_config#$1_storage_gas_StorageGasConfig($rsc)))) > 0) ==> ($x#$1_storage_gas_Point(ReadVec($points#$1_storage_gas_GasCurve($write_curve#$1_storage_gas_UsageGasConfig($byte_config#$1_storage_gas_StorageGasConfig($rsc))), (LenVec($points#$1_storage_gas_GasCurve($write_curve#$1_storage_gas_UsageGasConfig($byte_config#$1_storage_gas_StorageGasConfig($rsc)))) - 1))) < 10000))) && (var $range_21 := $Range(0, (LenVec($points#$1_storage_gas_GasCurve($write_curve#$1_storage_gas_UsageGasConfig($byte_config#$1_storage_gas_StorageGasConfig($rsc)))) - 1)); (forall $i_22: int :: $InRange($range_21, $i_22) ==> (var i := $i_22;
    ((($x#$1_storage_gas_Point(ReadVec($points#$1_storage_gas_GasCurve($write_curve#$1_storage_gas_UsageGasConfig($byte_config#$1_storage_gas_StorageGasConfig($rsc))), i)) < $x#$1_storage_gas_Point(ReadVec($points#$1_storage_gas_GasCurve($write_curve#$1_storage_gas_UsageGasConfig($byte_config#$1_storage_gas_StorageGasConfig($rsc))), (i + 1)))) && ($y#$1_storage_gas_Point(ReadVec($points#$1_storage_gas_GasCurve($write_curve#$1_storage_gas_UsageGasConfig($byte_config#$1_storage_gas_StorageGasConfig($rsc))), i)) <= $y#$1_storage_gas_Point(ReadVec($points#$1_storage_gas_GasCurve($write_curve#$1_storage_gas_UsageGasConfig($byte_config#$1_storage_gas_StorageGasConfig($rsc))), (i + 1))))))))))) && (var $range_23 := $points#$1_storage_gas_GasCurve($write_curve#$1_storage_gas_UsageGasConfig($byte_config#$1_storage_gas_StorageGasConfig($rsc))); (forall $i_24: int :: InRangeVec($range_23, $i_24) ==> (var $elem := ReadVec($range_23, $i_24);
    ((($x#$1_storage_gas_Point($elem) <= 10000) && ($y#$1_storage_gas_Point($elem) <= 10000)))))))))));

    // assume forall $rsc: ResourceDomain<reconfiguration::Configuration>(): WellFormed($rsc) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:397:5+1
    assume (forall $a_0: int :: {$ResourceValue($1_reconfiguration_Configuration_$memory, $a_0)}(var $rsc := $ResourceValue($1_reconfiguration_Configuration_$memory, $a_0);
    ($IsValid'$1_reconfiguration_Configuration'($rsc))));

    // assume forall $rsc: ResourceDomain<aptos_governance::ApprovedExecutionHashes>(): WellFormed($rsc) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:397:5+1
    assume (forall $a_0: int :: {$ResourceValue($1_aptos_governance_ApprovedExecutionHashes_$memory, $a_0)}(var $rsc := $ResourceValue($1_aptos_governance_ApprovedExecutionHashes_$memory, $a_0);
    ($IsValid'$1_aptos_governance_ApprovedExecutionHashes'($rsc))));

    // assume forall $rsc: ResourceDomain<aptos_governance::GovernanceResponsbility>(): WellFormed($rsc) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:397:5+1
    assume (forall $a_0: int :: {$ResourceValue($1_aptos_governance_GovernanceResponsbility_$memory, $a_0)}(var $rsc := $ResourceValue($1_aptos_governance_GovernanceResponsbility_$memory, $a_0);
    ($IsValid'$1_aptos_governance_GovernanceResponsbility'($rsc))));

    // assume forall $rsc: ResourceDomain<block::BlockResource>(): WellFormed($rsc) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:397:5+1
    assume (forall $a_0: int :: {$ResourceValue($1_block_BlockResource_$memory, $a_0)}(var $rsc := $ResourceValue($1_block_BlockResource_$memory, $a_0);
    ($IsValid'$1_block_BlockResource'($rsc))));

    // assume Implies(chain_status::$is_operating(), exists<timestamp::CurrentTimeMicroseconds>(1)) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:397:5+881
    // global invariant at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/timestamp.spec.move:4:9+93
    assume ($1_chain_status_$is_operating($1_chain_status_GenesisEndMarker_$memory) ==> $ResourceExists($1_timestamp_CurrentTimeMicroseconds_$memory, 1));

    // assume Implies(chain_status::$is_operating(), exists<staking_config::StakingConfig>(1)) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:397:5+881
    // global invariant at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/configs/staking_config.spec.move:4:9+83
    assume ($1_chain_status_$is_operating($1_chain_status_GenesisEndMarker_$memory) ==> $ResourceExists($1_staking_config_StakingConfig_$memory, 1));

    // assume Implies(chain_status::$is_operating(), exists<stake::AptosCoinCapabilities>(1)) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:397:5+881
    // global invariant at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/stake.spec.move:11:9+105
    assume ($1_chain_status_$is_operating($1_chain_status_GenesisEndMarker_$memory) ==> $ResourceExists($1_stake_AptosCoinCapabilities_$memory, 1));

    // assume Implies(chain_status::$is_operating(), exists<stake::ValidatorPerformance>(1)) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:397:5+881
    // global invariant at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/stake.spec.move:12:9+104
    assume ($1_chain_status_$is_operating($1_chain_status_GenesisEndMarker_$memory) ==> $ResourceExists($1_stake_ValidatorPerformance_$memory, 1));

    // assume Implies(chain_status::$is_operating(), exists<stake::ValidatorSet>(1)) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:397:5+881
    // global invariant at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/stake.spec.move:13:9+96
    assume ($1_chain_status_$is_operating($1_chain_status_GenesisEndMarker_$memory) ==> $ResourceExists($1_stake_ValidatorSet_$memory, 1));

    // assume Implies(chain_status::$is_operating(), exists<transaction_fee::AptosCoinCapabilities>(1)) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:397:5+881
    // global invariant at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/transaction_fee.spec.move:7:9+105
    assume ($1_chain_status_$is_operating($1_chain_status_GenesisEndMarker_$memory) ==> $ResourceExists($1_transaction_fee_AptosCoinCapabilities_$memory, 1));

    // assume Implies(chain_status::$is_operating(), exists<state_storage::StateStorageUsage>(1)) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:397:5+881
    // global invariant at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/state_storage.spec.move:7:9+101
    assume ($1_chain_status_$is_operating($1_chain_status_GenesisEndMarker_$memory) ==> $ResourceExists($1_state_storage_StateStorageUsage_$memory, 1));

    // assume Implies(chain_status::$is_operating(), exists<state_storage::GasParameter>(1)) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:397:5+881
    // global invariant at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/state_storage.spec.move:8:9+96
    assume ($1_chain_status_$is_operating($1_chain_status_GenesisEndMarker_$memory) ==> $ResourceExists($1_state_storage_GasParameter_$memory, 1));

    // assume Implies(chain_status::$is_operating(), exists<storage_gas::StorageGasConfig>(1)) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:397:5+881
    // global invariant at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/storage_gas.spec.move:34:9+100
    assume ($1_chain_status_$is_operating($1_chain_status_GenesisEndMarker_$memory) ==> $ResourceExists($1_storage_gas_StorageGasConfig_$memory, 1));

    // assume Implies(chain_status::$is_operating(), exists<storage_gas::StorageGas>(1)) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:397:5+881
    // global invariant at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/storage_gas.spec.move:35:9+94
    assume ($1_chain_status_$is_operating($1_chain_status_GenesisEndMarker_$memory) ==> $ResourceExists($1_storage_gas_StorageGas_$memory, 1));

    // assume Implies(chain_status::$is_operating(), exists<reconfiguration::Configuration>(1)) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:397:5+881
    // global invariant at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/reconfiguration.spec.move:7:9+97
    assume ($1_chain_status_$is_operating($1_chain_status_GenesisEndMarker_$memory) ==> $ResourceExists($1_reconfiguration_Configuration_$memory, 1));

    // assume Implies(chain_status::$is_operating(), Ge(timestamp::spec_now_microseconds(), reconfiguration::$last_reconfiguration_time())) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:397:5+881
    // global invariant at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/reconfiguration.spec.move:8:9+137
    assume ($1_chain_status_$is_operating($1_chain_status_GenesisEndMarker_$memory) ==> ($1_timestamp_spec_now_microseconds($1_timestamp_CurrentTimeMicroseconds_$memory) >= $1_reconfiguration_$last_reconfiguration_time($1_reconfiguration_Configuration_$memory)));

    // assume Implies(chain_status::$is_operating(), exists<block::BlockResource>(1)) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:397:5+881
    // global invariant at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/block.spec.move:5:9+97
    assume ($1_chain_status_$is_operating($1_chain_status_GenesisEndMarker_$memory) ==> $ResourceExists($1_block_BlockResource_$memory, 1));

    // assume Identical($t3, global<voting::VotingForum<governance_proposal::GovernanceProposal>>(1)) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.spec.move:537:9+85
    assume {:print "$at(3,30299,30384)"} true;
    assume ($t3 == $ResourceValue($1_voting_VotingForum'$1_governance_proposal_GovernanceProposal'_$memory, 1));

    // assume Identical($t4, table::spec_get<u64, voting::Proposal<governance_proposal::GovernanceProposal>>(select voting::VotingForum.proposals($t3), $t0)) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.spec.move:538:9+68
    assume {:print "$at(3,30393,30461)"} true;
    assume ($t4 == $1_table_spec_get'u64_$1_voting_Proposal'$1_governance_proposal_GovernanceProposal''($proposals#$1_voting_VotingForum'$1_governance_proposal_GovernanceProposal'($t3), $t0));

    // assume Identical($t5, string::$utf8([73, 83, 95, 77, 85, 76, 84, 73, 95, 83, 84, 69, 80, 95, 80, 82, 79, 80, 79, 83, 65, 76, 95, 73, 78, 95, 69, 88, 69, 67, 85, 84, 73, 79, 78])) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.spec.move:543:9+88
    assume {:print "$at(3,30769,30857)"} true;
    assume ($t5 == $1_string_$utf8(ConcatVec(ConcatVec(ConcatVec(ConcatVec(ConcatVec(ConcatVec(ConcatVec(ConcatVec(MakeVec4(73, 83, 95, 77), MakeVec4(85, 76, 84, 73)), MakeVec4(95, 83, 84, 69)), MakeVec4(80, 95, 80, 82)), MakeVec4(79, 80, 79, 83)), MakeVec4(65, 76, 95, 73)), MakeVec4(78, 95, 69, 88)), MakeVec4(69, 67, 85, 84)), MakeVec3(73, 79, 78))));

    // assume Identical($t6, string::$utf8([73, 83, 95, 77, 85, 76, 84, 73, 95, 83, 84, 69, 80, 95, 80, 82, 79, 80, 79, 83, 65, 76, 95, 75, 69, 89])) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.spec.move:550:9+62
    assume {:print "$at(3,31435,31497)"} true;
    assume ($t6 == $1_string_$utf8(ConcatVec(ConcatVec(ConcatVec(ConcatVec(ConcatVec(ConcatVec(MakeVec4(73, 83, 95, 77), MakeVec4(85, 76, 84, 73)), MakeVec4(95, 83, 84, 69)), MakeVec4(80, 95, 80, 82)), MakeVec4(79, 80, 79, 83)), MakeVec4(65, 76, 95, 75)), MakeVec2(69, 89))));

    // assume Identical($t7, And(simple_map::spec_contains_key<string::String, vector<u8>>(select voting::Proposal.metadata($t4), $t6), from_bcs::deserialize<bool>(simple_map::spec_get<string::String, vector<u8>>(select voting::Proposal.metadata($t4), $t6)))) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.spec.move:553:9+213
    assume {:print "$at(3,31721,31934)"} true;
    assume ($t7 == ($1_simple_map_spec_contains_key'$1_string_String_vec'u8''($metadata#$1_voting_Proposal'$1_governance_proposal_GovernanceProposal'($t4), $t6) && $1_from_bcs_deserialize'bool'($1_simple_map_spec_get'$1_string_String_vec'u8''($metadata#$1_voting_Proposal'$1_governance_proposal_GovernanceProposal'($t4), $t6))));

    // assume Identical($t8, Eq<num>(Len<u8>($t2), 0)) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.spec.move:555:9+65
    assume {:print "$at(3,31943,32008)"} true;
    assume ($t8 == $IsEqual'num'(LenVec($t2), 0));

    // assume Identical($t9, select aptos_governance::ApprovedExecutionHashes.hashes(global<aptos_governance::ApprovedExecutionHashes>(1))) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.spec.move:571:9+79
    assume {:print "$at(3,33171,33250)"} true;
    assume ($t9 == $hashes#$1_aptos_governance_ApprovedExecutionHashes($ResourceValue($1_aptos_governance_ApprovedExecutionHashes_$memory, 1)));

    // assume Identical($t10, global<aptos_governance::GovernanceResponsbility>(1)) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.spec.move:583:9+82
    assume {:print "$at(3,33841,33923)"} true;
    assume ($t10 == $ResourceValue($1_aptos_governance_GovernanceResponsbility_$memory, 1));

    // assume Identical($t11, simple_map::spec_get<address, account::SignerCapability>(select aptos_governance::GovernanceResponsbility.signer_caps($t10), $t1)) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.spec.move:584:9+93
    assume {:print "$at(3,33932,34025)"} true;
    assume ($t11 == $1_simple_map_spec_get'address_$1_account_SignerCapability'($signer_caps#$1_aptos_governance_GovernanceResponsbility($t10), $t1));

    // assume Identical($t12, select account::SignerCapability.account($t11)) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.spec.move:585:9+30
    assume {:print "$at(3,34034,34064)"} true;
    assume ($t12 == $account#$1_account_SignerCapability($t11));

    // assume Identical($t13, global<voting::VotingForum<governance_proposal::GovernanceProposal>>(1)) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.spec.move:593:9+85
    assume {:print "$at(3,34302,34387)"} true;
    assume ($t13 == $ResourceValue($1_voting_VotingForum'$1_governance_proposal_GovernanceProposal'_$memory, 1));

    // assume Identical($t14, table::spec_get<u64, voting::Proposal<governance_proposal::GovernanceProposal>>(select voting::VotingForum.proposals($t13), $t0)) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.spec.move:594:9+68
    assume {:print "$at(3,34396,34464)"} true;
    assume ($t14 == $1_table_spec_get'u64_$1_voting_Proposal'$1_governance_proposal_GovernanceProposal''($proposals#$1_voting_VotingForum'$1_governance_proposal_GovernanceProposal'($t13), $t0));

    // assume Identical($t15, option::spec_borrow<u128>(select voting::Proposal.early_resolution_vote_threshold($t14))) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.spec.move:596:9+95
    assume {:print "$at(3,34551,34646)"} true;
    assume ($t15 == $1_option_spec_borrow'u128'($early_resolution_vote_threshold#$1_voting_Proposal'$1_governance_proposal_GovernanceProposal'($t14)));

    // assume Identical($t16, Gt(timestamp::$now_seconds(), select voting::Proposal.expiration_secs($t14))) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.spec.move:597:9+77
    assume {:print "$at(3,34655,34732)"} true;
    assume ($t16 == ($1_timestamp_$now_seconds($1_timestamp_CurrentTimeMicroseconds_$memory) > $expiration_secs#$1_voting_Proposal'$1_governance_proposal_GovernanceProposal'($t14)));

    // assume Identical($t17, And(option::spec_is_some<u128>(select voting::Proposal.early_resolution_vote_threshold($t14)), Or(Ge(select voting::Proposal.yes_votes($t14), $t15), Ge(select voting::Proposal.no_votes($t14), $t15)))) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.spec.move:598:9+266
    assume {:print "$at(3,34741,35007)"} true;
    assume ($t17 == ($1_option_spec_is_some'u128'($early_resolution_vote_threshold#$1_voting_Proposal'$1_governance_proposal_GovernanceProposal'($t14)) && (($yes_votes#$1_voting_Proposal'$1_governance_proposal_GovernanceProposal'($t14) >= $t15) || ($no_votes#$1_voting_Proposal'$1_governance_proposal_GovernanceProposal'($t14) >= $t15))));

    // assume Identical($t18, Or($t16, $t17)) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.spec.move:601:9+60
    assume {:print "$at(3,35016,35076)"} true;
    assume ($t18 == ($t16 || $t17));

    // assume Identical($t19, from_bcs::deserialize<u64>(simple_map::spec_get<string::String, vector<u8>>(select voting::Proposal.metadata($t14), string::$utf8([82, 69, 83, 79, 76, 86, 65, 66, 76, 69, 95, 84, 73, 77, 69, 95, 77, 69, 84, 65, 68, 65, 84, 65, 95, 75, 69, 89])))) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.spec.move:610:9+145
    assume {:print "$at(3,35553,35698)"} true;
    assume ($t19 == $1_from_bcs_deserialize'u64'($1_simple_map_spec_get'$1_string_String_vec'u8''($metadata#$1_voting_Proposal'$1_governance_proposal_GovernanceProposal'($t14), $1_string_$utf8(ConcatVec(ConcatVec(ConcatVec(ConcatVec(ConcatVec(ConcatVec(MakeVec4(82, 69, 83, 79), MakeVec4(76, 86, 65, 66)), MakeVec4(76, 69, 95, 84)), MakeVec4(73, 77, 69, 95)), MakeVec4(77, 69, 84, 65)), MakeVec4(68, 65, 84, 65)), MakeVec4(95, 75, 69, 89))))));

    // assume Identical($t20, select aptos_governance::GovernanceResponsbility.signer_caps(global<aptos_governance::GovernanceResponsbility>(1))) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.spec.move:489:9+76
    assume {:print "$at(3,27938,28014)"} true;
    assume ($t20 == $signer_caps#$1_aptos_governance_GovernanceResponsbility($ResourceValue($1_aptos_governance_GovernanceResponsbility_$memory, 1)));

    // assume chain_status::$is_operating() at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.spec.move:524:9+38
    assume {:print "$at(3,29649,29687)"} true;
    assume $1_chain_status_$is_operating($1_chain_status_GenesisEndMarker_$memory);

    // @28 := save_mem(timestamp::CurrentTimeMicroseconds) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.spec.move:524:9+38
    $1_timestamp_CurrentTimeMicroseconds_$memory#28 := $1_timestamp_CurrentTimeMicroseconds_$memory;

    // @27 := save_mem(voting::VotingForum<governance_proposal::GovernanceProposal>) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.spec.move:524:9+38
    $1_voting_VotingForum'$1_governance_proposal_GovernanceProposal'_$memory#27 := $1_voting_VotingForum'$1_governance_proposal_GovernanceProposal'_$memory;

    // @29 := save_mem(aptos_governance::ApprovedExecutionHashes) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.spec.move:524:9+38
    $1_aptos_governance_ApprovedExecutionHashes_$memory#29 := $1_aptos_governance_ApprovedExecutionHashes_$memory;

    // @30 := save_mem(aptos_governance::GovernanceResponsbility) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.spec.move:524:9+38
    $1_aptos_governance_GovernanceResponsbility_$memory#30 := $1_aptos_governance_GovernanceResponsbility_$memory;

    // trace_local[proposal_id]($t0) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:397:5+1
    assume {:print "$at(2,17872,17873)"} true;
    assume {:print "$track_local(44,16,0):", $t0} $t0 == $t0;

    // trace_local[signer_address]($t1) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:397:5+1
    assume {:print "$track_local(44,16,1):", $t1} $t1 == $t1;

    // trace_local[next_execution_hash]($t2) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:397:5+1
    assume {:print "$track_local(44,16,2):", $t2} $t2 == $t2;

    // $t21 := 0x1 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:398:57+16
    assume {:print "$at(2,18111,18127)"} true;
    $t21 := 1;
    assume $IsValid'address'($t21);

    // assume Identical($t22, global<voting::VotingForum<governance_proposal::GovernanceProposal>>($t21)) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.spec.move:286:9+75
    assume {:print "$at(154,12822,12897)"} true;
    assume ($t22 == $ResourceValue($1_voting_VotingForum'$1_governance_proposal_GovernanceProposal'_$memory, $t21));

    // assert chain_status::$is_operating() at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.spec.move:163:9+38
    assume {:print "$at(154,8035,8073)"} true;
    assert {:msg "assert_failed(154,8035,8073): precondition does not hold at this call"}
      $1_chain_status_$is_operating($1_chain_status_GenesisEndMarker_$memory);

    // voting::resolve_proposal_v2<governance_proposal::GovernanceProposal>($t21, $t0, $t2) on_abort goto L4 with $t23 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:398:9+99
    assume {:print "$at(2,18063,18162)"} true;
    call $1_voting_resolve_proposal_v2'$1_governance_proposal_GovernanceProposal'($t21, $t0, $t2);
    if ($abort_flag) {
        assume {:print "$at(2,18063,18162)"} true;
        $t23 := $abort_code;
        assume {:print "$track_abort(44,16):", $t23} $t23 == $t23;
        goto L4;
    }

    // $t24 := vector::length<u8>($t2) on_abort goto L4 with $t23 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:401:13+36
    assume {:print "$at(2,18336,18372)"} true;
    call $t24 := $1_vector_length'u8'($t2);
    if ($abort_flag) {
        assume {:print "$at(2,18336,18372)"} true;
        $t23 := $abort_code;
        assume {:print "$track_abort(44,16):", $t23} $t23 == $t23;
        goto L4;
    }

    // $t25 := 0 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:401:53+1
    $t25 := 0;
    assume $IsValid'u64'($t25);

    // $t26 := ==($t24, $t25) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:401:50+2
    $t26 := $IsEqual'u64'($t24, $t25);

    // if ($t26) goto L1 else goto L0 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:401:9+379
    if ($t26) { goto L1; } else { goto L0; }

    // label L1 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:402:34+11
    assume {:print "$at(2,18414,18425)"} true;
L1:

    // assume Identical($t27, global<voting::VotingForum<governance_proposal::GovernanceProposal>>(1)) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.spec.move:427:9+85
    assume {:print "$at(3,24612,24697)"} true;
    assume ($t27 == $ResourceValue($1_voting_VotingForum'$1_governance_proposal_GovernanceProposal'_$memory, 1));

    // assume Identical($t28, table::spec_get<u64, voting::Proposal<governance_proposal::GovernanceProposal>>(select voting::VotingForum.proposals($t27), $t0)) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.spec.move:430:9+68
    assume {:print "$at(3,24870,24938)"} true;
    assume ($t28 == $1_table_spec_get'u64_$1_voting_Proposal'$1_governance_proposal_GovernanceProposal''($proposals#$1_voting_VotingForum'$1_governance_proposal_GovernanceProposal'($t27), $t0));

    // aptos_governance::remove_approved_hash($t0) on_abort goto L4 with $t23 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:402:13+33
    assume {:print "$at(2,18393,18426)"} true;
    call $1_aptos_governance_remove_approved_hash($t0);
    if ($abort_flag) {
        assume {:print "$at(2,18393,18426)"} true;
        $t23 := $abort_code;
        assume {:print "$track_abort(44,16):", $t23} $t23 == $t23;
        goto L4;
    }

    // goto L2 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:402:46+1
    goto L2;

    // label L0 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:407:38+11
    assume {:print "$at(2,18689,18700)"} true;
L0:

    // assume Identical($t29, global<voting::VotingForum<governance_proposal::GovernanceProposal>>(1)) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.spec.move:368:9+85
    assume {:print "$at(3,20710,20795)"} true;
    assume ($t29 == $ResourceValue($1_voting_VotingForum'$1_governance_proposal_GovernanceProposal'_$memory, 1));

    // assume Identical($t30, table::spec_get<u64, voting::Proposal<governance_proposal::GovernanceProposal>>(select voting::VotingForum.proposals($t29), $t0)) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.spec.move:369:9+68
    assume {:print "$at(3,20804,20872)"} true;
    assume ($t30 == $1_table_spec_get'u64_$1_voting_Proposal'$1_governance_proposal_GovernanceProposal''($proposals#$1_voting_VotingForum'$1_governance_proposal_GovernanceProposal'($t29), $t0));

    // assume Identical($t31, option::spec_borrow<u128>(select voting::Proposal.early_resolution_vote_threshold($t30))) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.spec.move:371:9+95
    assume {:print "$at(3,20959,21054)"} true;
    assume ($t31 == $1_option_spec_borrow'u128'($early_resolution_vote_threshold#$1_voting_Proposal'$1_governance_proposal_GovernanceProposal'($t30)));

    // assert chain_status::$is_operating() at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.spec.move:351:9+38
    assume {:print "$at(3,20149,20187)"} true;
    assert {:msg "assert_failed(3,20149,20187): precondition does not hold at this call"}
      $1_chain_status_$is_operating($1_chain_status_GenesisEndMarker_$memory);

    // aptos_governance::add_approved_script_hash($t0) on_abort goto L4 with $t23 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:407:13+37
    assume {:print "$at(2,18664,18701)"} true;
    call $1_aptos_governance_add_approved_script_hash($t0);
    if ($abort_flag) {
        assume {:print "$at(2,18664,18701)"} true;
        $t23 := $abort_code;
        assume {:print "$track_abort(44,16):", $t23} $t23 == $t23;
        goto L4;
    }

    // label L2 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:409:20+14
    assume {:print "$at(2,18732,18746)"} true;
L2:

    // assume Identical($t32, select aptos_governance::GovernanceResponsbility.signer_caps(global<aptos_governance::GovernanceResponsbility>(1))) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.spec.move:489:9+76
    assume {:print "$at(3,27938,28014)"} true;
    assume ($t32 == $signer_caps#$1_aptos_governance_GovernanceResponsbility($ResourceValue($1_aptos_governance_GovernanceResponsbility_$memory, 1)));

    // $t33 := aptos_governance::get_signer($t1) on_abort goto L4 with $t23 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:409:9+26
    assume {:print "$at(2,18721,18747)"} true;
    call $t33 := $1_aptos_governance_get_signer($t1);
    if ($abort_flag) {
        assume {:print "$at(2,18721,18747)"} true;
        $t23 := $abort_code;
        assume {:print "$track_abort(44,16):", $t23} $t23 == $t23;
        goto L4;
    }

    // trace_return[0]($t33) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:409:9+26
    assume {:print "$track_return(44,16,0):", $t33} $t33 == $t33;

    // label L3 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:410:5+1
    assume {:print "$at(2,18752,18753)"} true;
L3:

    // assume Identical($t34, global<voting::VotingForum<governance_proposal::GovernanceProposal>>(1)) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.spec.move:539:9+95
    assume {:print "$at(3,30470,30565)"} true;
    assume ($t34 == $ResourceValue($1_voting_VotingForum'$1_governance_proposal_GovernanceProposal'_$memory, 1));

    // assume Identical($t35, table::spec_get<u64, voting::Proposal<governance_proposal::GovernanceProposal>>(select voting::VotingForum.proposals($t34), $t0)) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.spec.move:540:9+83
    assume {:print "$at(3,30574,30657)"} true;
    assume ($t35 == $1_table_spec_get'u64_$1_voting_Proposal'$1_governance_proposal_GovernanceProposal''($proposals#$1_voting_VotingForum'$1_governance_proposal_GovernanceProposal'($t34), $t0));

    // assume Identical($t36, simple_map::spec_get<string::String, vector<u8>>(select voting::Proposal.metadata($t35), $t5)) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.spec.move:544:9+127
    assume {:print "$at(3,30866,30993)"} true;
    assume ($t36 == $1_simple_map_spec_get'$1_string_String_vec'u8''($metadata#$1_voting_Proposal'$1_governance_proposal_GovernanceProposal'($t35), $t5));

    // assume Identical($t37, select aptos_governance::ApprovedExecutionHashes.hashes(global<aptos_governance::ApprovedExecutionHashes>(1))) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.spec.move:572:9+89
    assume {:print "$at(3,33259,33348)"} true;
    assume ($t37 == $hashes#$1_aptos_governance_ApprovedExecutionHashes($ResourceValue($1_aptos_governance_ApprovedExecutionHashes_$memory, 1)));

    // assert Not(Not(exists[@27]<voting::VotingForum<governance_proposal::GovernanceProposal>>(1))) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.spec.move:592:9+77
    assume {:print "$at(3,34216,34293)"} true;
    assert {:msg "assert_failed(3,34216,34293): function does not abort under this condition"}
      !!$ResourceExists($1_voting_VotingForum'$1_governance_proposal_GovernanceProposal'_$memory#27, 1);

    // assert Not(Not(table::spec_contains[]<u64, voting::Proposal<governance_proposal::GovernanceProposal>>(select voting::VotingForum.proposals($t13), $t0))) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.spec.move:595:9+69
    assume {:print "$at(3,34473,34542)"} true;
    assert {:msg "assert_failed(3,34473,34542): function does not abort under this condition"}
      !!$1_table_spec_contains'u64_$1_voting_Proposal'$1_governance_proposal_GovernanceProposal''($proposals#$1_voting_VotingForum'$1_governance_proposal_GovernanceProposal'($t13), $t0);

    // assert Not(And($t18, Or(Le(select voting::Proposal.yes_votes($t14), select voting::Proposal.no_votes($t14)), Lt(Add(select voting::Proposal.yes_votes($t14), select voting::Proposal.no_votes($t14)), select voting::Proposal.min_vote_threshold($t14))))) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.spec.move:603:9+141
    assume {:print "$at(3,35104,35245)"} true;
    assert {:msg "assert_failed(3,35104,35245): function does not abort under this condition"}
      !($t18 && (($yes_votes#$1_voting_Proposal'$1_governance_proposal_GovernanceProposal'($t14) <= $no_votes#$1_voting_Proposal'$1_governance_proposal_GovernanceProposal'($t14)) || (($yes_votes#$1_voting_Proposal'$1_governance_proposal_GovernanceProposal'($t14) + $no_votes#$1_voting_Proposal'$1_governance_proposal_GovernanceProposal'($t14)) < $min_vote_threshold#$1_voting_Proposal'$1_governance_proposal_GovernanceProposal'($t14))));

    // assert Not(Not($t18)) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.spec.move:605:9+25
    assume {:print "$at(3,35274,35299)"} true;
    assert {:msg "assert_failed(3,35274,35299): function does not abort under this condition"}
      !!$t18;

    // assert Not(select voting::Proposal.is_resolved($t14)) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.spec.move:607:9+31
    assume {:print "$at(3,35309,35340)"} true;
    assert {:msg "assert_failed(3,35309,35340): function does not abort under this condition"}
      !$is_resolved#$1_voting_Proposal'$1_governance_proposal_GovernanceProposal'($t14);

    // assert Not(Not(string::spec_internal_check_utf8[]([82, 69, 83, 79, 76, 86, 65, 66, 76, 69, 95, 84, 73, 77, 69, 95, 77, 69, 84, 65, 68, 65, 84, 65, 95, 75, 69, 89]))) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.spec.move:608:9+82
    assume {:print "$at(3,35349,35431)"} true;
    assert {:msg "assert_failed(3,35349,35431): function does not abort under this condition"}
      !!$1_string_spec_internal_check_utf8(ConcatVec(ConcatVec(ConcatVec(ConcatVec(ConcatVec(ConcatVec(MakeVec4(82, 69, 83, 79), MakeVec4(76, 86, 65, 66)), MakeVec4(76, 69, 95, 84)), MakeVec4(73, 77, 69, 95)), MakeVec4(77, 69, 84, 65)), MakeVec4(68, 65, 84, 65)), MakeVec4(95, 75, 69, 89)));

    // assert Not(Not(simple_map::spec_contains_key[]<string::String, vector<u8>>(select voting::Proposal.metadata($t14), string::$utf8[]([82, 69, 83, 79, 76, 86, 65, 66, 76, 69, 95, 84, 73, 77, 69, 95, 77, 69, 84, 65, 68, 65, 84, 65, 95, 75, 69, 89])))) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.spec.move:609:9+104
    assume {:print "$at(3,35440,35544)"} true;
    assert {:msg "assert_failed(3,35440,35544): function does not abort under this condition"}
      !!$1_simple_map_spec_contains_key'$1_string_String_vec'u8''($metadata#$1_voting_Proposal'$1_governance_proposal_GovernanceProposal'($t14), $1_string_$utf8(ConcatVec(ConcatVec(ConcatVec(ConcatVec(ConcatVec(ConcatVec(MakeVec4(82, 69, 83, 79), MakeVec4(76, 86, 65, 66)), MakeVec4(76, 69, 95, 84)), MakeVec4(73, 77, 69, 95)), MakeVec4(77, 69, 84, 65)), MakeVec4(68, 65, 84, 65)), MakeVec4(95, 75, 69, 89))));

    // assert Not(Not(from_bcs::deserializable[]<u64>(simple_map::spec_get[]<string::String, vector<u8>>(select voting::Proposal.metadata($t14), string::$utf8[]([82, 69, 83, 79, 76, 86, 65, 66, 76, 69, 95, 84, 73, 77, 69, 95, 77, 69, 84, 65, 68, 65, 84, 65, 95, 75, 69, 89]))))) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.spec.move:611:9+137
    assume {:print "$at(3,35707,35844)"} true;
    assert {:msg "assert_failed(3,35707,35844): function does not abort under this condition"}
      !!$1_from_bcs_deserializable'u64'($1_simple_map_spec_get'$1_string_String_vec'u8''($metadata#$1_voting_Proposal'$1_governance_proposal_GovernanceProposal'($t14), $1_string_$utf8(ConcatVec(ConcatVec(ConcatVec(ConcatVec(ConcatVec(ConcatVec(MakeVec4(82, 69, 83, 79), MakeVec4(76, 86, 65, 66)), MakeVec4(76, 69, 95, 84)), MakeVec4(73, 77, 69, 95)), MakeVec4(77, 69, 84, 65)), MakeVec4(68, 65, 84, 65)), MakeVec4(95, 75, 69, 89)))));

    // assert Not(Le(timestamp::$now_seconds[@28](), $t19)) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.spec.move:612:9+54
    assume {:print "$at(3,35853,35907)"} true;
    assert {:msg "assert_failed(3,35853,35907): function does not abort under this condition"}
      !($1_timestamp_$now_seconds($1_timestamp_CurrentTimeMicroseconds_$memory#28) <= $t19);

    // assert Not(Neq<vector<u8>>(transaction_context::spec_get_script_hash[](), select voting::Proposal.execution_hash($t14))) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.spec.move:613:9+98
    assume {:print "$at(3,35916,36014)"} true;
    assert {:msg "assert_failed(3,35916,36014): function does not abort under this condition"}
      !!$IsEqual'vec'u8''($1_transaction_context_spec_get_script_hash(), $execution_hash#$1_voting_Proposal'$1_governance_proposal_GovernanceProposal'($t14));

    // assert Not(Not(string::spec_internal_check_utf8[]([73, 83, 95, 77, 85, 76, 84, 73, 95, 83, 84, 69, 80, 95, 80, 82, 79, 80, 79, 83, 65, 76, 95, 73, 78, 95, 69, 88, 69, 67, 85, 84, 73, 79, 78]))) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.spec.move:542:9+93
    assume {:print "$at(3,30667,30760)"} true;
    assert {:msg "assert_failed(3,30667,30760): function does not abort under this condition"}
      !!$1_string_spec_internal_check_utf8(ConcatVec(ConcatVec(ConcatVec(ConcatVec(ConcatVec(ConcatVec(ConcatVec(ConcatVec(MakeVec4(73, 83, 95, 77), MakeVec4(85, 76, 84, 73)), MakeVec4(95, 83, 84, 69)), MakeVec4(80, 95, 80, 82)), MakeVec4(79, 80, 79, 83)), MakeVec4(65, 76, 95, 73)), MakeVec4(78, 95, 69, 88)), MakeVec4(69, 67, 85, 84)), MakeVec3(73, 79, 78)));

    // assert Not(Not(string::spec_internal_check_utf8[]([73, 83, 95, 77, 85, 76, 84, 73, 95, 83, 84, 69, 80, 95, 80, 82, 79, 80, 79, 83, 65, 76, 95, 75, 69, 89]))) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.spec.move:549:9+80
    assume {:print "$at(3,31346,31426)"} true;
    assert {:msg "assert_failed(3,31346,31426): function does not abort under this condition"}
      !!$1_string_spec_internal_check_utf8(ConcatVec(ConcatVec(ConcatVec(ConcatVec(ConcatVec(ConcatVec(MakeVec4(73, 83, 95, 77), MakeVec4(85, 76, 84, 73)), MakeVec4(95, 83, 84, 69)), MakeVec4(80, 95, 80, 82)), MakeVec4(79, 80, 79, 83)), MakeVec4(65, 76, 95, 75)), MakeVec2(69, 89)));

    // assert Not(And(simple_map::spec_contains_key[]<string::String, vector<u8>>(select voting::Proposal.metadata($t4), $t6), from_bcs::deserializable[]<bool>(simple_map::spec_get[]<string::String, vector<u8>>(select voting::Proposal.metadata($t4), $t6)))) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.spec.move:551:9+206
    assume {:print "$at(3,31506,31712)"} true;
    assert {:msg "assert_failed(3,31506,31712): function does not abort under this condition"}
      !($1_simple_map_spec_contains_key'$1_string_String_vec'u8''($metadata#$1_voting_Proposal'$1_governance_proposal_GovernanceProposal'($t4), $t6) && $1_from_bcs_deserializable'bool'($1_simple_map_spec_get'$1_string_String_vec'u8''($metadata#$1_voting_Proposal'$1_governance_proposal_GovernanceProposal'($t4), $t6)));

    // assert Not(And(Not($t7), Not($t8))) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.spec.move:556:9+58
    assume {:print "$at(3,32017,32075)"} true;
    assert {:msg "assert_failed(3,32017,32075): function does not abort under this condition"}
      !(!$t7 && !$t8);

    // assert Not(And(And($t8, $t7), Not(simple_map::spec_contains_key[]<string::String, vector<u8>>(select voting::Proposal.metadata($t4), $t5)))) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.spec.move:557:9+138
    assume {:print "$at(3,32084,32222)"} true;
    assert {:msg "assert_failed(3,32084,32222): function does not abort under this condition"}
      !(($t8 && $t7) && !$1_simple_map_spec_contains_key'$1_string_String_vec'u8''($metadata#$1_voting_Proposal'$1_governance_proposal_GovernanceProposal'($t4), $t5));

    // assert Not(And($t8, Not(exists[@29]<aptos_governance::ApprovedExecutionHashes>(1)))) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.spec.move:570:9+93
    assume {:print "$at(3,33069,33162)"} true;
    assert {:msg "assert_failed(3,33069,33162): function does not abort under this condition"}
      !($t8 && !$ResourceExists($1_aptos_governance_ApprovedExecutionHashes_$memory#29, 1));

    // assert Not(Not(exists[@30]<aptos_governance::GovernanceResponsbility>(1))) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.spec.move:488:9+61
    assume {:print "$at(3,27868,27929)"} true;
    assert {:msg "assert_failed(3,27868,27929): function does not abort under this condition"}
      !!$ResourceExists($1_aptos_governance_GovernanceResponsbility_$memory#30, 1);

    // assert Not(Not(simple_map::spec_contains_key[]<address, account::SignerCapability>($t20, $t1))) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.spec.move:490:9+66
    assume {:print "$at(3,28023,28089)"} true;
    assert {:msg "assert_failed(3,28023,28089): function does not abort under this condition"}
      !!$1_simple_map_spec_contains_key'address_$1_account_SignerCapability'($t20, $t1);

    // assert Implies(simple_map::spec_contains_key<string::String, vector<u8>>(select voting::Proposal.metadata($t4), $t5), Eq<vector<u8>>($t36, bcs::serialize<bool>(true))) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.spec.move:546:9+173
    assume {:print "$at(3,31163,31336)"} true;
    assert {:msg "assert_failed(3,31163,31336): post-condition does not hold"}
      ($1_simple_map_spec_contains_key'$1_string_String_vec'u8''($metadata#$1_voting_Proposal'$1_governance_proposal_GovernanceProposal'($t4), $t5) ==> $IsEqual'vec'u8''($t36, $1_bcs_serialize'bool'(true)));

    // assert Implies($t8, And(And(Eq<bool>(select voting::Proposal.is_resolved($t35), true), Eq<u64>(select voting::Proposal.resolution_time_secs($t35), timestamp::spec_now_seconds())), (if $t7 {Eq<vector<u8>>($t36, bcs::serialize<bool>(false))} else {Implies(simple_map::spec_contains_key<string::String, vector<u8>>(select voting::Proposal.metadata($t4), $t5), Eq<vector<u8>>($t36, bcs::serialize<bool>(true)))}))) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.spec.move:558:9+495
    assume {:print "$at(3,32236,32731)"} true;
    assert {:msg "assert_failed(3,32236,32731): post-condition does not hold"}
      ($t8 ==> (($IsEqual'bool'($is_resolved#$1_voting_Proposal'$1_governance_proposal_GovernanceProposal'($t35), true) && $IsEqual'u64'($resolution_time_secs#$1_voting_Proposal'$1_governance_proposal_GovernanceProposal'($t35), $1_timestamp_spec_now_seconds($1_timestamp_CurrentTimeMicroseconds_$memory))) && (if ($t7) then ($IsEqual'vec'u8''($t36, $1_bcs_serialize'bool'(false))) else (($1_simple_map_spec_contains_key'$1_string_String_vec'u8''($metadata#$1_voting_Proposal'$1_governance_proposal_GovernanceProposal'($t4), $t5) ==> $IsEqual'vec'u8''($t36, $1_bcs_serialize'bool'(true)))))));

    // assert Implies(Implies(Not($t8), And(Eq<vector<u8>>(select voting::Proposal.execution_hash($t35), $t2), simple_map::spec_contains_key<string::String, vector<u8>>(select voting::Proposal.metadata($t4), $t5))), Eq<vector<u8>>($t36, bcs::serialize<bool>(true))) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.spec.move:565:9+279
    assume {:print "$at(3,32740,33019)"} true;
    assert {:msg "assert_failed(3,32740,33019): post-condition does not hold"}
      ((!$t8 ==> ($IsEqual'vec'u8''($execution_hash#$1_voting_Proposal'$1_governance_proposal_GovernanceProposal'($t35), $t2) && $1_simple_map_spec_contains_key'$1_string_String_vec'u8''($metadata#$1_voting_Proposal'$1_governance_proposal_GovernanceProposal'($t4), $t5))) ==> $IsEqual'vec'u8''($t36, $1_bcs_serialize'bool'(true)));

    // assert Implies($t8, Not(simple_map::spec_contains_key<u64, vector<u8>>($t37, $t0))) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.spec.move:573:9+107
    assume {:print "$at(3,33357,33464)"} true;
    assert {:msg "assert_failed(3,33357,33464): post-condition does not hold"}
      ($t8 ==> !$1_simple_map_spec_contains_key'u64_vec'u8''($t37, $t0));

    // assert Implies(Not($t8), Eq<vector<u8>>(simple_map::spec_get<u64, vector<u8>>($t37, $t0), $t2)) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.spec.move:578:9+133
    assume {:print "$at(3,33633,33766)"} true;
    assert {:msg "assert_failed(3,33633,33766): post-condition does not hold"}
      (!$t8 ==> $IsEqual'vec'u8''($1_simple_map_spec_get'u64_vec'u8''($t37, $t0), $t2));

    // assert Eq<address>(signer::$address_of($t33), $t12) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.spec.move:586:9+43
    assume {:print "$at(3,34073,34116)"} true;
    assert {:msg "assert_failed(3,34073,34116): post-condition does not hold"}
      $IsEqual'address'($1_signer_$address_of($t33), $t12);

    // return $t33 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.spec.move:586:9+43
    $ret0 := $t33;
    return;

    // label L4 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:410:5+1
    assume {:print "$at(2,18752,18753)"} true;
L4:

    // assert Or(Or(Or(Or(Or(Or(Or(Or(Or(Or(Or(Or(Or(Or(Or(Or(Or(Not(exists[@27]<voting::VotingForum<governance_proposal::GovernanceProposal>>(1)), Not(table::spec_contains[]<u64, voting::Proposal<governance_proposal::GovernanceProposal>>(select voting::VotingForum.proposals($t13), $t0))), And($t18, Or(Le(select voting::Proposal.yes_votes($t14), select voting::Proposal.no_votes($t14)), Lt(Add(select voting::Proposal.yes_votes($t14), select voting::Proposal.no_votes($t14)), select voting::Proposal.min_vote_threshold($t14))))), Not($t18)), select voting::Proposal.is_resolved($t14)), Not(string::spec_internal_check_utf8[]([82, 69, 83, 79, 76, 86, 65, 66, 76, 69, 95, 84, 73, 77, 69, 95, 77, 69, 84, 65, 68, 65, 84, 65, 95, 75, 69, 89]))), Not(simple_map::spec_contains_key[]<string::String, vector<u8>>(select voting::Proposal.metadata($t14), string::$utf8[]([82, 69, 83, 79, 76, 86, 65, 66, 76, 69, 95, 84, 73, 77, 69, 95, 77, 69, 84, 65, 68, 65, 84, 65, 95, 75, 69, 89])))), Not(from_bcs::deserializable[]<u64>(simple_map::spec_get[]<string::String, vector<u8>>(select voting::Proposal.metadata($t14), string::$utf8[]([82, 69, 83, 79, 76, 86, 65, 66, 76, 69, 95, 84, 73, 77, 69, 95, 77, 69, 84, 65, 68, 65, 84, 65, 95, 75, 69, 89]))))), Le(timestamp::$now_seconds[@28](), $t19)), Neq<vector<u8>>(transaction_context::spec_get_script_hash[](), select voting::Proposal.execution_hash($t14))), Not(string::spec_internal_check_utf8[]([73, 83, 95, 77, 85, 76, 84, 73, 95, 83, 84, 69, 80, 95, 80, 82, 79, 80, 79, 83, 65, 76, 95, 73, 78, 95, 69, 88, 69, 67, 85, 84, 73, 79, 78]))), Not(string::spec_internal_check_utf8[]([73, 83, 95, 77, 85, 76, 84, 73, 95, 83, 84, 69, 80, 95, 80, 82, 79, 80, 79, 83, 65, 76, 95, 75, 69, 89]))), And(simple_map::spec_contains_key[]<string::String, vector<u8>>(select voting::Proposal.metadata($t4), $t6), from_bcs::deserializable[]<bool>(simple_map::spec_get[]<string::String, vector<u8>>(select voting::Proposal.metadata($t4), $t6)))), And(Not($t7), Not($t8))), And(And($t8, $t7), Not(simple_map::spec_contains_key[]<string::String, vector<u8>>(select voting::Proposal.metadata($t4), $t5)))), And($t8, Not(exists[@29]<aptos_governance::ApprovedExecutionHashes>(1)))), Not(exists[@30]<aptos_governance::GovernanceResponsbility>(1))), Not(simple_map::spec_contains_key[]<address, account::SignerCapability>($t20, $t1))) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.spec.move:514:5+5194
    assume {:print "$at(3,28928,34122)"} true;
    assert {:msg "assert_failed(3,28928,34122): abort not covered by any of the `aborts_if` clauses"}
      (((((((((((((((((!$ResourceExists($1_voting_VotingForum'$1_governance_proposal_GovernanceProposal'_$memory#27, 1) || !$1_table_spec_contains'u64_$1_voting_Proposal'$1_governance_proposal_GovernanceProposal''($proposals#$1_voting_VotingForum'$1_governance_proposal_GovernanceProposal'($t13), $t0)) || ($t18 && (($yes_votes#$1_voting_Proposal'$1_governance_proposal_GovernanceProposal'($t14) <= $no_votes#$1_voting_Proposal'$1_governance_proposal_GovernanceProposal'($t14)) || (($yes_votes#$1_voting_Proposal'$1_governance_proposal_GovernanceProposal'($t14) + $no_votes#$1_voting_Proposal'$1_governance_proposal_GovernanceProposal'($t14)) < $min_vote_threshold#$1_voting_Proposal'$1_governance_proposal_GovernanceProposal'($t14))))) || !$t18) || $is_resolved#$1_voting_Proposal'$1_governance_proposal_GovernanceProposal'($t14)) || !$1_string_spec_internal_check_utf8(ConcatVec(ConcatVec(ConcatVec(ConcatVec(ConcatVec(ConcatVec(MakeVec4(82, 69, 83, 79), MakeVec4(76, 86, 65, 66)), MakeVec4(76, 69, 95, 84)), MakeVec4(73, 77, 69, 95)), MakeVec4(77, 69, 84, 65)), MakeVec4(68, 65, 84, 65)), MakeVec4(95, 75, 69, 89)))) || !$1_simple_map_spec_contains_key'$1_string_String_vec'u8''($metadata#$1_voting_Proposal'$1_governance_proposal_GovernanceProposal'($t14), $1_string_$utf8(ConcatVec(ConcatVec(ConcatVec(ConcatVec(ConcatVec(ConcatVec(MakeVec4(82, 69, 83, 79), MakeVec4(76, 86, 65, 66)), MakeVec4(76, 69, 95, 84)), MakeVec4(73, 77, 69, 95)), MakeVec4(77, 69, 84, 65)), MakeVec4(68, 65, 84, 65)), MakeVec4(95, 75, 69, 89))))) || !$1_from_bcs_deserializable'u64'($1_simple_map_spec_get'$1_string_String_vec'u8''($metadata#$1_voting_Proposal'$1_governance_proposal_GovernanceProposal'($t14), $1_string_$utf8(ConcatVec(ConcatVec(ConcatVec(ConcatVec(ConcatVec(ConcatVec(MakeVec4(82, 69, 83, 79), MakeVec4(76, 86, 65, 66)), MakeVec4(76, 69, 95, 84)), MakeVec4(73, 77, 69, 95)), MakeVec4(77, 69, 84, 65)), MakeVec4(68, 65, 84, 65)), MakeVec4(95, 75, 69, 89)))))) || ($1_timestamp_$now_seconds($1_timestamp_CurrentTimeMicroseconds_$memory#28) <= $t19)) || !$IsEqual'vec'u8''($1_transaction_context_spec_get_script_hash(), $execution_hash#$1_voting_Proposal'$1_governance_proposal_GovernanceProposal'($t14))) || !$1_string_spec_internal_check_utf8(ConcatVec(ConcatVec(ConcatVec(ConcatVec(ConcatVec(ConcatVec(ConcatVec(ConcatVec(MakeVec4(73, 83, 95, 77), MakeVec4(85, 76, 84, 73)), MakeVec4(95, 83, 84, 69)), MakeVec4(80, 95, 80, 82)), MakeVec4(79, 80, 79, 83)), MakeVec4(65, 76, 95, 73)), MakeVec4(78, 95, 69, 88)), MakeVec4(69, 67, 85, 84)), MakeVec3(73, 79, 78)))) || !$1_string_spec_internal_check_utf8(ConcatVec(ConcatVec(ConcatVec(ConcatVec(ConcatVec(ConcatVec(MakeVec4(73, 83, 95, 77), MakeVec4(85, 76, 84, 73)), MakeVec4(95, 83, 84, 69)), MakeVec4(80, 95, 80, 82)), MakeVec4(79, 80, 79, 83)), MakeVec4(65, 76, 95, 75)), MakeVec2(69, 89)))) || ($1_simple_map_spec_contains_key'$1_string_String_vec'u8''($metadata#$1_voting_Proposal'$1_governance_proposal_GovernanceProposal'($t4), $t6) && $1_from_bcs_deserializable'bool'($1_simple_map_spec_get'$1_string_String_vec'u8''($metadata#$1_voting_Proposal'$1_governance_proposal_GovernanceProposal'($t4), $t6)))) || (!$t7 && !$t8)) || (($t8 && $t7) && !$1_simple_map_spec_contains_key'$1_string_String_vec'u8''($metadata#$1_voting_Proposal'$1_governance_proposal_GovernanceProposal'($t4), $t5))) || ($t8 && !$ResourceExists($1_aptos_governance_ApprovedExecutionHashes_$memory#29, 1))) || !$ResourceExists($1_aptos_governance_GovernanceResponsbility_$memory#30, 1)) || !$1_simple_map_spec_contains_key'address_$1_account_SignerCapability'($t20, $t1));

    // abort($t23) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.spec.move:514:5+5194
    $abort_code := $t23;
    $abort_flag := true;
    return;

}

// struct block::BlockResource at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/block.move:22:5+369
type {:datatype} $1_block_BlockResource;
function {:constructor} $1_block_BlockResource($height: int, $epoch_interval: int, $new_block_events: $1_event_EventHandle'$1_block_NewBlockEvent', $update_epoch_interval_events: $1_event_EventHandle'$1_block_UpdateEpochIntervalEvent'): $1_block_BlockResource;
function {:inline} $Update'$1_block_BlockResource'_height(s: $1_block_BlockResource, x: int): $1_block_BlockResource {
    $1_block_BlockResource(x, $epoch_interval#$1_block_BlockResource(s), $new_block_events#$1_block_BlockResource(s), $update_epoch_interval_events#$1_block_BlockResource(s))
}
function {:inline} $Update'$1_block_BlockResource'_epoch_interval(s: $1_block_BlockResource, x: int): $1_block_BlockResource {
    $1_block_BlockResource($height#$1_block_BlockResource(s), x, $new_block_events#$1_block_BlockResource(s), $update_epoch_interval_events#$1_block_BlockResource(s))
}
function {:inline} $Update'$1_block_BlockResource'_new_block_events(s: $1_block_BlockResource, x: $1_event_EventHandle'$1_block_NewBlockEvent'): $1_block_BlockResource {
    $1_block_BlockResource($height#$1_block_BlockResource(s), $epoch_interval#$1_block_BlockResource(s), x, $update_epoch_interval_events#$1_block_BlockResource(s))
}
function {:inline} $Update'$1_block_BlockResource'_update_epoch_interval_events(s: $1_block_BlockResource, x: $1_event_EventHandle'$1_block_UpdateEpochIntervalEvent'): $1_block_BlockResource {
    $1_block_BlockResource($height#$1_block_BlockResource(s), $epoch_interval#$1_block_BlockResource(s), $new_block_events#$1_block_BlockResource(s), x)
}
function $IsValid'$1_block_BlockResource'(s: $1_block_BlockResource): bool {
    $IsValid'u64'($height#$1_block_BlockResource(s))
      && $IsValid'u64'($epoch_interval#$1_block_BlockResource(s))
      && $IsValid'$1_event_EventHandle'$1_block_NewBlockEvent''($new_block_events#$1_block_BlockResource(s))
      && $IsValid'$1_event_EventHandle'$1_block_UpdateEpochIntervalEvent''($update_epoch_interval_events#$1_block_BlockResource(s))
}
function {:inline} $IsEqual'$1_block_BlockResource'(s1: $1_block_BlockResource, s2: $1_block_BlockResource): bool {
    s1 == s2
}
var $1_block_BlockResource_$memory: $Memory $1_block_BlockResource;

// struct block::NewBlockEvent at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/block.move:33:5+345
type {:datatype} $1_block_NewBlockEvent;
function {:constructor} $1_block_NewBlockEvent($hash: int, $epoch: int, $round: int, $height: int, $previous_block_votes_bitvec: Vec (int), $proposer: int, $failed_proposer_indices: Vec (int), $time_microseconds: int): $1_block_NewBlockEvent;
function {:inline} $Update'$1_block_NewBlockEvent'_hash(s: $1_block_NewBlockEvent, x: int): $1_block_NewBlockEvent {
    $1_block_NewBlockEvent(x, $epoch#$1_block_NewBlockEvent(s), $round#$1_block_NewBlockEvent(s), $height#$1_block_NewBlockEvent(s), $previous_block_votes_bitvec#$1_block_NewBlockEvent(s), $proposer#$1_block_NewBlockEvent(s), $failed_proposer_indices#$1_block_NewBlockEvent(s), $time_microseconds#$1_block_NewBlockEvent(s))
}
function {:inline} $Update'$1_block_NewBlockEvent'_epoch(s: $1_block_NewBlockEvent, x: int): $1_block_NewBlockEvent {
    $1_block_NewBlockEvent($hash#$1_block_NewBlockEvent(s), x, $round#$1_block_NewBlockEvent(s), $height#$1_block_NewBlockEvent(s), $previous_block_votes_bitvec#$1_block_NewBlockEvent(s), $proposer#$1_block_NewBlockEvent(s), $failed_proposer_indices#$1_block_NewBlockEvent(s), $time_microseconds#$1_block_NewBlockEvent(s))
}
function {:inline} $Update'$1_block_NewBlockEvent'_round(s: $1_block_NewBlockEvent, x: int): $1_block_NewBlockEvent {
    $1_block_NewBlockEvent($hash#$1_block_NewBlockEvent(s), $epoch#$1_block_NewBlockEvent(s), x, $height#$1_block_NewBlockEvent(s), $previous_block_votes_bitvec#$1_block_NewBlockEvent(s), $proposer#$1_block_NewBlockEvent(s), $failed_proposer_indices#$1_block_NewBlockEvent(s), $time_microseconds#$1_block_NewBlockEvent(s))
}
function {:inline} $Update'$1_block_NewBlockEvent'_height(s: $1_block_NewBlockEvent, x: int): $1_block_NewBlockEvent {
    $1_block_NewBlockEvent($hash#$1_block_NewBlockEvent(s), $epoch#$1_block_NewBlockEvent(s), $round#$1_block_NewBlockEvent(s), x, $previous_block_votes_bitvec#$1_block_NewBlockEvent(s), $proposer#$1_block_NewBlockEvent(s), $failed_proposer_indices#$1_block_NewBlockEvent(s), $time_microseconds#$1_block_NewBlockEvent(s))
}
function {:inline} $Update'$1_block_NewBlockEvent'_previous_block_votes_bitvec(s: $1_block_NewBlockEvent, x: Vec (int)): $1_block_NewBlockEvent {
    $1_block_NewBlockEvent($hash#$1_block_NewBlockEvent(s), $epoch#$1_block_NewBlockEvent(s), $round#$1_block_NewBlockEvent(s), $height#$1_block_NewBlockEvent(s), x, $proposer#$1_block_NewBlockEvent(s), $failed_proposer_indices#$1_block_NewBlockEvent(s), $time_microseconds#$1_block_NewBlockEvent(s))
}
function {:inline} $Update'$1_block_NewBlockEvent'_proposer(s: $1_block_NewBlockEvent, x: int): $1_block_NewBlockEvent {
    $1_block_NewBlockEvent($hash#$1_block_NewBlockEvent(s), $epoch#$1_block_NewBlockEvent(s), $round#$1_block_NewBlockEvent(s), $height#$1_block_NewBlockEvent(s), $previous_block_votes_bitvec#$1_block_NewBlockEvent(s), x, $failed_proposer_indices#$1_block_NewBlockEvent(s), $time_microseconds#$1_block_NewBlockEvent(s))
}
function {:inline} $Update'$1_block_NewBlockEvent'_failed_proposer_indices(s: $1_block_NewBlockEvent, x: Vec (int)): $1_block_NewBlockEvent {
    $1_block_NewBlockEvent($hash#$1_block_NewBlockEvent(s), $epoch#$1_block_NewBlockEvent(s), $round#$1_block_NewBlockEvent(s), $height#$1_block_NewBlockEvent(s), $previous_block_votes_bitvec#$1_block_NewBlockEvent(s), $proposer#$1_block_NewBlockEvent(s), x, $time_microseconds#$1_block_NewBlockEvent(s))
}
function {:inline} $Update'$1_block_NewBlockEvent'_time_microseconds(s: $1_block_NewBlockEvent, x: int): $1_block_NewBlockEvent {
    $1_block_NewBlockEvent($hash#$1_block_NewBlockEvent(s), $epoch#$1_block_NewBlockEvent(s), $round#$1_block_NewBlockEvent(s), $height#$1_block_NewBlockEvent(s), $previous_block_votes_bitvec#$1_block_NewBlockEvent(s), $proposer#$1_block_NewBlockEvent(s), $failed_proposer_indices#$1_block_NewBlockEvent(s), x)
}
function $IsValid'$1_block_NewBlockEvent'(s: $1_block_NewBlockEvent): bool {
    $IsValid'address'($hash#$1_block_NewBlockEvent(s))
      && $IsValid'u64'($epoch#$1_block_NewBlockEvent(s))
      && $IsValid'u64'($round#$1_block_NewBlockEvent(s))
      && $IsValid'u64'($height#$1_block_NewBlockEvent(s))
      && $IsValid'vec'u8''($previous_block_votes_bitvec#$1_block_NewBlockEvent(s))
      && $IsValid'address'($proposer#$1_block_NewBlockEvent(s))
      && $IsValid'vec'u64''($failed_proposer_indices#$1_block_NewBlockEvent(s))
      && $IsValid'u64'($time_microseconds#$1_block_NewBlockEvent(s))
}
function {:inline} $IsEqual'$1_block_NewBlockEvent'(s1: $1_block_NewBlockEvent, s2: $1_block_NewBlockEvent): bool {
    $IsEqual'address'($hash#$1_block_NewBlockEvent(s1), $hash#$1_block_NewBlockEvent(s2))
    && $IsEqual'u64'($epoch#$1_block_NewBlockEvent(s1), $epoch#$1_block_NewBlockEvent(s2))
    && $IsEqual'u64'($round#$1_block_NewBlockEvent(s1), $round#$1_block_NewBlockEvent(s2))
    && $IsEqual'u64'($height#$1_block_NewBlockEvent(s1), $height#$1_block_NewBlockEvent(s2))
    && $IsEqual'vec'u8''($previous_block_votes_bitvec#$1_block_NewBlockEvent(s1), $previous_block_votes_bitvec#$1_block_NewBlockEvent(s2))
    && $IsEqual'address'($proposer#$1_block_NewBlockEvent(s1), $proposer#$1_block_NewBlockEvent(s2))
    && $IsEqual'vec'u64''($failed_proposer_indices#$1_block_NewBlockEvent(s1), $failed_proposer_indices#$1_block_NewBlockEvent(s2))
    && $IsEqual'u64'($time_microseconds#$1_block_NewBlockEvent(s1), $time_microseconds#$1_block_NewBlockEvent(s2))}

// struct block::UpdateEpochIntervalEvent at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/block.move:46:5+121
type {:datatype} $1_block_UpdateEpochIntervalEvent;
function {:constructor} $1_block_UpdateEpochIntervalEvent($old_epoch_interval: int, $new_epoch_interval: int): $1_block_UpdateEpochIntervalEvent;
function {:inline} $Update'$1_block_UpdateEpochIntervalEvent'_old_epoch_interval(s: $1_block_UpdateEpochIntervalEvent, x: int): $1_block_UpdateEpochIntervalEvent {
    $1_block_UpdateEpochIntervalEvent(x, $new_epoch_interval#$1_block_UpdateEpochIntervalEvent(s))
}
function {:inline} $Update'$1_block_UpdateEpochIntervalEvent'_new_epoch_interval(s: $1_block_UpdateEpochIntervalEvent, x: int): $1_block_UpdateEpochIntervalEvent {
    $1_block_UpdateEpochIntervalEvent($old_epoch_interval#$1_block_UpdateEpochIntervalEvent(s), x)
}
function $IsValid'$1_block_UpdateEpochIntervalEvent'(s: $1_block_UpdateEpochIntervalEvent): bool {
    $IsValid'u64'($old_epoch_interval#$1_block_UpdateEpochIntervalEvent(s))
      && $IsValid'u64'($new_epoch_interval#$1_block_UpdateEpochIntervalEvent(s))
}
function {:inline} $IsEqual'$1_block_UpdateEpochIntervalEvent'(s1: $1_block_UpdateEpochIntervalEvent, s2: $1_block_UpdateEpochIntervalEvent): bool {
    s1 == s2
}
