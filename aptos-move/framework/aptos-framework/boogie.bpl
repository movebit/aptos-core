
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
// Native Vector implementation for element type `$1_aggregator_Aggregator`

// Not inlined. It appears faster this way.
function $IsEqual'vec'$1_aggregator_Aggregator''(v1: Vec ($1_aggregator_Aggregator), v2: Vec ($1_aggregator_Aggregator)): bool {
    LenVec(v1) == LenVec(v2) &&
    (forall i: int:: InRangeVec(v1, i) ==> $IsEqual'$1_aggregator_Aggregator'(ReadVec(v1, i), ReadVec(v2, i)))
}

// Not inlined.
function $IsPrefix'vec'$1_aggregator_Aggregator''(v: Vec ($1_aggregator_Aggregator), prefix: Vec ($1_aggregator_Aggregator)): bool {
    LenVec(v) >= LenVec(prefix) &&
    (forall i: int:: InRangeVec(prefix, i) ==> $IsEqual'$1_aggregator_Aggregator'(ReadVec(v, i), ReadVec(prefix, i)))
}

// Not inlined.
function $IsSuffix'vec'$1_aggregator_Aggregator''(v: Vec ($1_aggregator_Aggregator), suffix: Vec ($1_aggregator_Aggregator)): bool {
    LenVec(v) >= LenVec(suffix) &&
    (forall i: int:: InRangeVec(suffix, i) ==> $IsEqual'$1_aggregator_Aggregator'(ReadVec(v, LenVec(v) - LenVec(suffix) + i), ReadVec(suffix, i)))
}

// Not inlined.
function $IsValid'vec'$1_aggregator_Aggregator''(v: Vec ($1_aggregator_Aggregator)): bool {
    $IsValid'u64'(LenVec(v)) &&
    (forall i: int:: InRangeVec(v, i) ==> $IsValid'$1_aggregator_Aggregator'(ReadVec(v, i)))
}


function {:inline} $ContainsVec'$1_aggregator_Aggregator'(v: Vec ($1_aggregator_Aggregator), e: $1_aggregator_Aggregator): bool {
    (exists i: int :: $IsValid'u64'(i) && InRangeVec(v, i) && $IsEqual'$1_aggregator_Aggregator'(ReadVec(v, i), e))
}

function $IndexOfVec'$1_aggregator_Aggregator'(v: Vec ($1_aggregator_Aggregator), e: $1_aggregator_Aggregator): int;
axiom (forall v: Vec ($1_aggregator_Aggregator), e: $1_aggregator_Aggregator:: {$IndexOfVec'$1_aggregator_Aggregator'(v, e)}
    (var i := $IndexOfVec'$1_aggregator_Aggregator'(v, e);
     if (!$ContainsVec'$1_aggregator_Aggregator'(v, e)) then i == -1
     else $IsValid'u64'(i) && InRangeVec(v, i) && $IsEqual'$1_aggregator_Aggregator'(ReadVec(v, i), e) &&
        (forall j: int :: $IsValid'u64'(j) && j >= 0 && j < i ==> !$IsEqual'$1_aggregator_Aggregator'(ReadVec(v, j), e))));


function {:inline} $RangeVec'$1_aggregator_Aggregator'(v: Vec ($1_aggregator_Aggregator)): $Range {
    $Range(0, LenVec(v))
}


function {:inline} $EmptyVec'$1_aggregator_Aggregator'(): Vec ($1_aggregator_Aggregator) {
    EmptyVec()
}

procedure {:inline 1} $1_vector_empty'$1_aggregator_Aggregator'() returns (v: Vec ($1_aggregator_Aggregator)) {
    v := EmptyVec();
}

function {:inline} $1_vector_$empty'$1_aggregator_Aggregator'(): Vec ($1_aggregator_Aggregator) {
    EmptyVec()
}

procedure {:inline 1} $1_vector_is_empty'$1_aggregator_Aggregator'(v: Vec ($1_aggregator_Aggregator)) returns (b: bool) {
    b := IsEmptyVec(v);
}

procedure {:inline 1} $1_vector_push_back'$1_aggregator_Aggregator'(m: $Mutation (Vec ($1_aggregator_Aggregator)), val: $1_aggregator_Aggregator) returns (m': $Mutation (Vec ($1_aggregator_Aggregator))) {
    m' := $UpdateMutation(m, ExtendVec($Dereference(m), val));
}

function {:inline} $1_vector_$push_back'$1_aggregator_Aggregator'(v: Vec ($1_aggregator_Aggregator), val: $1_aggregator_Aggregator): Vec ($1_aggregator_Aggregator) {
    ExtendVec(v, val)
}

procedure {:inline 1} $1_vector_pop_back'$1_aggregator_Aggregator'(m: $Mutation (Vec ($1_aggregator_Aggregator))) returns (e: $1_aggregator_Aggregator, m': $Mutation (Vec ($1_aggregator_Aggregator))) {
    var v: Vec ($1_aggregator_Aggregator);
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

procedure {:inline 1} $1_vector_append'$1_aggregator_Aggregator'(m: $Mutation (Vec ($1_aggregator_Aggregator)), other: Vec ($1_aggregator_Aggregator)) returns (m': $Mutation (Vec ($1_aggregator_Aggregator))) {
    m' := $UpdateMutation(m, ConcatVec($Dereference(m), other));
}

procedure {:inline 1} $1_vector_reverse'$1_aggregator_Aggregator'(m: $Mutation (Vec ($1_aggregator_Aggregator))) returns (m': $Mutation (Vec ($1_aggregator_Aggregator))) {
    m' := $UpdateMutation(m, ReverseVec($Dereference(m)));
}

procedure {:inline 1} $1_vector_reverse_append'$1_aggregator_Aggregator'(m: $Mutation (Vec ($1_aggregator_Aggregator)), other: Vec ($1_aggregator_Aggregator)) returns (m': $Mutation (Vec ($1_aggregator_Aggregator))) {
    m' := $UpdateMutation(m, ConcatVec($Dereference(m), ReverseVec(other)));
}

procedure {:inline 1} $1_vector_trim_reverse'$1_aggregator_Aggregator'(m: $Mutation (Vec ($1_aggregator_Aggregator)), new_len: int) returns (v: (Vec ($1_aggregator_Aggregator)), m': $Mutation (Vec ($1_aggregator_Aggregator))) {
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

procedure {:inline 1} $1_vector_trim'$1_aggregator_Aggregator'(m: $Mutation (Vec ($1_aggregator_Aggregator)), new_len: int) returns (v: (Vec ($1_aggregator_Aggregator)), m': $Mutation (Vec ($1_aggregator_Aggregator))) {
    var len: int;
    v := $Dereference(m);
    if (LenVec(v) < new_len) {
        call $ExecFailureAbort();
        return;
    }
    v := SliceVec(v, new_len, LenVec(v));
    m' := $UpdateMutation(m, SliceVec($Dereference(m), 0, new_len));
}

procedure {:inline 1} $1_vector_reverse_slice'$1_aggregator_Aggregator'(m: $Mutation (Vec ($1_aggregator_Aggregator)), left: int, right: int) returns (m': $Mutation (Vec ($1_aggregator_Aggregator))) {
    var left_vec: Vec ($1_aggregator_Aggregator);
    var mid_vec: Vec ($1_aggregator_Aggregator);
    var right_vec: Vec ($1_aggregator_Aggregator);
    var v: Vec ($1_aggregator_Aggregator);
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

procedure {:inline 1} $1_vector_rotate'$1_aggregator_Aggregator'(m: $Mutation (Vec ($1_aggregator_Aggregator)), rot: int) returns (n: int, m': $Mutation (Vec ($1_aggregator_Aggregator))) {
    var v: Vec ($1_aggregator_Aggregator);
    var len: int;
    var left_vec: Vec ($1_aggregator_Aggregator);
    var right_vec: Vec ($1_aggregator_Aggregator);
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

procedure {:inline 1} $1_vector_rotate_slice'$1_aggregator_Aggregator'(m: $Mutation (Vec ($1_aggregator_Aggregator)), left: int, rot: int, right: int) returns (n: int, m': $Mutation (Vec ($1_aggregator_Aggregator))) {
    var left_vec: Vec ($1_aggregator_Aggregator);
    var mid_vec: Vec ($1_aggregator_Aggregator);
    var right_vec: Vec ($1_aggregator_Aggregator);
    var mid_left_vec: Vec ($1_aggregator_Aggregator);
    var mid_right_vec: Vec ($1_aggregator_Aggregator);
    var v: Vec ($1_aggregator_Aggregator);
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

procedure {:inline 1} $1_vector_insert'$1_aggregator_Aggregator'(m: $Mutation (Vec ($1_aggregator_Aggregator)), i: int, e: $1_aggregator_Aggregator) returns (m': $Mutation (Vec ($1_aggregator_Aggregator))) {
    var left_vec: Vec ($1_aggregator_Aggregator);
    var right_vec: Vec ($1_aggregator_Aggregator);
    var v: Vec ($1_aggregator_Aggregator);
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

procedure {:inline 1} $1_vector_length'$1_aggregator_Aggregator'(v: Vec ($1_aggregator_Aggregator)) returns (l: int) {
    l := LenVec(v);
}

function {:inline} $1_vector_$length'$1_aggregator_Aggregator'(v: Vec ($1_aggregator_Aggregator)): int {
    LenVec(v)
}

procedure {:inline 1} $1_vector_borrow'$1_aggregator_Aggregator'(v: Vec ($1_aggregator_Aggregator), i: int) returns (dst: $1_aggregator_Aggregator) {
    if (!InRangeVec(v, i)) {
        call $ExecFailureAbort();
        return;
    }
    dst := ReadVec(v, i);
}

function {:inline} $1_vector_$borrow'$1_aggregator_Aggregator'(v: Vec ($1_aggregator_Aggregator), i: int): $1_aggregator_Aggregator {
    ReadVec(v, i)
}

procedure {:inline 1} $1_vector_borrow_mut'$1_aggregator_Aggregator'(m: $Mutation (Vec ($1_aggregator_Aggregator)), index: int)
returns (dst: $Mutation ($1_aggregator_Aggregator), m': $Mutation (Vec ($1_aggregator_Aggregator)))
{
    var v: Vec ($1_aggregator_Aggregator);
    v := $Dereference(m);
    if (!InRangeVec(v, index)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Mutation(l#$Mutation(m), ExtendVec(p#$Mutation(m), index), ReadVec(v, index));
    m' := m;
}

function {:inline} $1_vector_$borrow_mut'$1_aggregator_Aggregator'(v: Vec ($1_aggregator_Aggregator), i: int): $1_aggregator_Aggregator {
    ReadVec(v, i)
}

procedure {:inline 1} $1_vector_destroy_empty'$1_aggregator_Aggregator'(v: Vec ($1_aggregator_Aggregator)) {
    if (!IsEmptyVec(v)) {
      call $ExecFailureAbort();
    }
}

procedure {:inline 1} $1_vector_swap'$1_aggregator_Aggregator'(m: $Mutation (Vec ($1_aggregator_Aggregator)), i: int, j: int) returns (m': $Mutation (Vec ($1_aggregator_Aggregator)))
{
    var v: Vec ($1_aggregator_Aggregator);
    v := $Dereference(m);
    if (!InRangeVec(v, i) || !InRangeVec(v, j)) {
        call $ExecFailureAbort();
        return;
    }
    m' := $UpdateMutation(m, SwapVec(v, i, j));
}

function {:inline} $1_vector_$swap'$1_aggregator_Aggregator'(v: Vec ($1_aggregator_Aggregator), i: int, j: int): Vec ($1_aggregator_Aggregator) {
    SwapVec(v, i, j)
}

procedure {:inline 1} $1_vector_remove'$1_aggregator_Aggregator'(m: $Mutation (Vec ($1_aggregator_Aggregator)), i: int) returns (e: $1_aggregator_Aggregator, m': $Mutation (Vec ($1_aggregator_Aggregator)))
{
    var v: Vec ($1_aggregator_Aggregator);

    v := $Dereference(m);

    if (!InRangeVec(v, i)) {
        call $ExecFailureAbort();
        return;
    }
    e := ReadVec(v, i);
    m' := $UpdateMutation(m, RemoveAtVec(v, i));
}

procedure {:inline 1} $1_vector_swap_remove'$1_aggregator_Aggregator'(m: $Mutation (Vec ($1_aggregator_Aggregator)), i: int) returns (e: $1_aggregator_Aggregator, m': $Mutation (Vec ($1_aggregator_Aggregator)))
{
    var len: int;
    var v: Vec ($1_aggregator_Aggregator);

    v := $Dereference(m);
    len := LenVec(v);
    if (!InRangeVec(v, i)) {
        call $ExecFailureAbort();
        return;
    }
    e := ReadVec(v, i);
    m' := $UpdateMutation(m, RemoveVec(SwapVec(v, i, len-1)));
}

procedure {:inline 1} $1_vector_contains'$1_aggregator_Aggregator'(v: Vec ($1_aggregator_Aggregator), e: $1_aggregator_Aggregator) returns (res: bool)  {
    res := $ContainsVec'$1_aggregator_Aggregator'(v, e);
}

procedure {:inline 1}
$1_vector_index_of'$1_aggregator_Aggregator'(v: Vec ($1_aggregator_Aggregator), e: $1_aggregator_Aggregator) returns (res1: bool, res2: int) {
    res2 := $IndexOfVec'$1_aggregator_Aggregator'(v, e);
    if (res2 >= 0) {
        res1 := true;
    } else {
        res1 := false;
        res2 := 0;
    }
}


// ----------------------------------------------------------------------------------
// Native Vector implementation for element type `$1_optional_aggregator_Integer`

// Not inlined. It appears faster this way.
function $IsEqual'vec'$1_optional_aggregator_Integer''(v1: Vec ($1_optional_aggregator_Integer), v2: Vec ($1_optional_aggregator_Integer)): bool {
    LenVec(v1) == LenVec(v2) &&
    (forall i: int:: InRangeVec(v1, i) ==> $IsEqual'$1_optional_aggregator_Integer'(ReadVec(v1, i), ReadVec(v2, i)))
}

// Not inlined.
function $IsPrefix'vec'$1_optional_aggregator_Integer''(v: Vec ($1_optional_aggregator_Integer), prefix: Vec ($1_optional_aggregator_Integer)): bool {
    LenVec(v) >= LenVec(prefix) &&
    (forall i: int:: InRangeVec(prefix, i) ==> $IsEqual'$1_optional_aggregator_Integer'(ReadVec(v, i), ReadVec(prefix, i)))
}

// Not inlined.
function $IsSuffix'vec'$1_optional_aggregator_Integer''(v: Vec ($1_optional_aggregator_Integer), suffix: Vec ($1_optional_aggregator_Integer)): bool {
    LenVec(v) >= LenVec(suffix) &&
    (forall i: int:: InRangeVec(suffix, i) ==> $IsEqual'$1_optional_aggregator_Integer'(ReadVec(v, LenVec(v) - LenVec(suffix) + i), ReadVec(suffix, i)))
}

// Not inlined.
function $IsValid'vec'$1_optional_aggregator_Integer''(v: Vec ($1_optional_aggregator_Integer)): bool {
    $IsValid'u64'(LenVec(v)) &&
    (forall i: int:: InRangeVec(v, i) ==> $IsValid'$1_optional_aggregator_Integer'(ReadVec(v, i)))
}


function {:inline} $ContainsVec'$1_optional_aggregator_Integer'(v: Vec ($1_optional_aggregator_Integer), e: $1_optional_aggregator_Integer): bool {
    (exists i: int :: $IsValid'u64'(i) && InRangeVec(v, i) && $IsEqual'$1_optional_aggregator_Integer'(ReadVec(v, i), e))
}

function $IndexOfVec'$1_optional_aggregator_Integer'(v: Vec ($1_optional_aggregator_Integer), e: $1_optional_aggregator_Integer): int;
axiom (forall v: Vec ($1_optional_aggregator_Integer), e: $1_optional_aggregator_Integer:: {$IndexOfVec'$1_optional_aggregator_Integer'(v, e)}
    (var i := $IndexOfVec'$1_optional_aggregator_Integer'(v, e);
     if (!$ContainsVec'$1_optional_aggregator_Integer'(v, e)) then i == -1
     else $IsValid'u64'(i) && InRangeVec(v, i) && $IsEqual'$1_optional_aggregator_Integer'(ReadVec(v, i), e) &&
        (forall j: int :: $IsValid'u64'(j) && j >= 0 && j < i ==> !$IsEqual'$1_optional_aggregator_Integer'(ReadVec(v, j), e))));


function {:inline} $RangeVec'$1_optional_aggregator_Integer'(v: Vec ($1_optional_aggregator_Integer)): $Range {
    $Range(0, LenVec(v))
}


function {:inline} $EmptyVec'$1_optional_aggregator_Integer'(): Vec ($1_optional_aggregator_Integer) {
    EmptyVec()
}

procedure {:inline 1} $1_vector_empty'$1_optional_aggregator_Integer'() returns (v: Vec ($1_optional_aggregator_Integer)) {
    v := EmptyVec();
}

function {:inline} $1_vector_$empty'$1_optional_aggregator_Integer'(): Vec ($1_optional_aggregator_Integer) {
    EmptyVec()
}

procedure {:inline 1} $1_vector_is_empty'$1_optional_aggregator_Integer'(v: Vec ($1_optional_aggregator_Integer)) returns (b: bool) {
    b := IsEmptyVec(v);
}

procedure {:inline 1} $1_vector_push_back'$1_optional_aggregator_Integer'(m: $Mutation (Vec ($1_optional_aggregator_Integer)), val: $1_optional_aggregator_Integer) returns (m': $Mutation (Vec ($1_optional_aggregator_Integer))) {
    m' := $UpdateMutation(m, ExtendVec($Dereference(m), val));
}

function {:inline} $1_vector_$push_back'$1_optional_aggregator_Integer'(v: Vec ($1_optional_aggregator_Integer), val: $1_optional_aggregator_Integer): Vec ($1_optional_aggregator_Integer) {
    ExtendVec(v, val)
}

procedure {:inline 1} $1_vector_pop_back'$1_optional_aggregator_Integer'(m: $Mutation (Vec ($1_optional_aggregator_Integer))) returns (e: $1_optional_aggregator_Integer, m': $Mutation (Vec ($1_optional_aggregator_Integer))) {
    var v: Vec ($1_optional_aggregator_Integer);
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

procedure {:inline 1} $1_vector_append'$1_optional_aggregator_Integer'(m: $Mutation (Vec ($1_optional_aggregator_Integer)), other: Vec ($1_optional_aggregator_Integer)) returns (m': $Mutation (Vec ($1_optional_aggregator_Integer))) {
    m' := $UpdateMutation(m, ConcatVec($Dereference(m), other));
}

procedure {:inline 1} $1_vector_reverse'$1_optional_aggregator_Integer'(m: $Mutation (Vec ($1_optional_aggregator_Integer))) returns (m': $Mutation (Vec ($1_optional_aggregator_Integer))) {
    m' := $UpdateMutation(m, ReverseVec($Dereference(m)));
}

procedure {:inline 1} $1_vector_reverse_append'$1_optional_aggregator_Integer'(m: $Mutation (Vec ($1_optional_aggregator_Integer)), other: Vec ($1_optional_aggregator_Integer)) returns (m': $Mutation (Vec ($1_optional_aggregator_Integer))) {
    m' := $UpdateMutation(m, ConcatVec($Dereference(m), ReverseVec(other)));
}

procedure {:inline 1} $1_vector_trim_reverse'$1_optional_aggregator_Integer'(m: $Mutation (Vec ($1_optional_aggregator_Integer)), new_len: int) returns (v: (Vec ($1_optional_aggregator_Integer)), m': $Mutation (Vec ($1_optional_aggregator_Integer))) {
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

procedure {:inline 1} $1_vector_trim'$1_optional_aggregator_Integer'(m: $Mutation (Vec ($1_optional_aggregator_Integer)), new_len: int) returns (v: (Vec ($1_optional_aggregator_Integer)), m': $Mutation (Vec ($1_optional_aggregator_Integer))) {
    var len: int;
    v := $Dereference(m);
    if (LenVec(v) < new_len) {
        call $ExecFailureAbort();
        return;
    }
    v := SliceVec(v, new_len, LenVec(v));
    m' := $UpdateMutation(m, SliceVec($Dereference(m), 0, new_len));
}

procedure {:inline 1} $1_vector_reverse_slice'$1_optional_aggregator_Integer'(m: $Mutation (Vec ($1_optional_aggregator_Integer)), left: int, right: int) returns (m': $Mutation (Vec ($1_optional_aggregator_Integer))) {
    var left_vec: Vec ($1_optional_aggregator_Integer);
    var mid_vec: Vec ($1_optional_aggregator_Integer);
    var right_vec: Vec ($1_optional_aggregator_Integer);
    var v: Vec ($1_optional_aggregator_Integer);
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

procedure {:inline 1} $1_vector_rotate'$1_optional_aggregator_Integer'(m: $Mutation (Vec ($1_optional_aggregator_Integer)), rot: int) returns (n: int, m': $Mutation (Vec ($1_optional_aggregator_Integer))) {
    var v: Vec ($1_optional_aggregator_Integer);
    var len: int;
    var left_vec: Vec ($1_optional_aggregator_Integer);
    var right_vec: Vec ($1_optional_aggregator_Integer);
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

procedure {:inline 1} $1_vector_rotate_slice'$1_optional_aggregator_Integer'(m: $Mutation (Vec ($1_optional_aggregator_Integer)), left: int, rot: int, right: int) returns (n: int, m': $Mutation (Vec ($1_optional_aggregator_Integer))) {
    var left_vec: Vec ($1_optional_aggregator_Integer);
    var mid_vec: Vec ($1_optional_aggregator_Integer);
    var right_vec: Vec ($1_optional_aggregator_Integer);
    var mid_left_vec: Vec ($1_optional_aggregator_Integer);
    var mid_right_vec: Vec ($1_optional_aggregator_Integer);
    var v: Vec ($1_optional_aggregator_Integer);
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

procedure {:inline 1} $1_vector_insert'$1_optional_aggregator_Integer'(m: $Mutation (Vec ($1_optional_aggregator_Integer)), i: int, e: $1_optional_aggregator_Integer) returns (m': $Mutation (Vec ($1_optional_aggregator_Integer))) {
    var left_vec: Vec ($1_optional_aggregator_Integer);
    var right_vec: Vec ($1_optional_aggregator_Integer);
    var v: Vec ($1_optional_aggregator_Integer);
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

procedure {:inline 1} $1_vector_length'$1_optional_aggregator_Integer'(v: Vec ($1_optional_aggregator_Integer)) returns (l: int) {
    l := LenVec(v);
}

function {:inline} $1_vector_$length'$1_optional_aggregator_Integer'(v: Vec ($1_optional_aggregator_Integer)): int {
    LenVec(v)
}

procedure {:inline 1} $1_vector_borrow'$1_optional_aggregator_Integer'(v: Vec ($1_optional_aggregator_Integer), i: int) returns (dst: $1_optional_aggregator_Integer) {
    if (!InRangeVec(v, i)) {
        call $ExecFailureAbort();
        return;
    }
    dst := ReadVec(v, i);
}

function {:inline} $1_vector_$borrow'$1_optional_aggregator_Integer'(v: Vec ($1_optional_aggregator_Integer), i: int): $1_optional_aggregator_Integer {
    ReadVec(v, i)
}

procedure {:inline 1} $1_vector_borrow_mut'$1_optional_aggregator_Integer'(m: $Mutation (Vec ($1_optional_aggregator_Integer)), index: int)
returns (dst: $Mutation ($1_optional_aggregator_Integer), m': $Mutation (Vec ($1_optional_aggregator_Integer)))
{
    var v: Vec ($1_optional_aggregator_Integer);
    v := $Dereference(m);
    if (!InRangeVec(v, index)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Mutation(l#$Mutation(m), ExtendVec(p#$Mutation(m), index), ReadVec(v, index));
    m' := m;
}

function {:inline} $1_vector_$borrow_mut'$1_optional_aggregator_Integer'(v: Vec ($1_optional_aggregator_Integer), i: int): $1_optional_aggregator_Integer {
    ReadVec(v, i)
}

procedure {:inline 1} $1_vector_destroy_empty'$1_optional_aggregator_Integer'(v: Vec ($1_optional_aggregator_Integer)) {
    if (!IsEmptyVec(v)) {
      call $ExecFailureAbort();
    }
}

procedure {:inline 1} $1_vector_swap'$1_optional_aggregator_Integer'(m: $Mutation (Vec ($1_optional_aggregator_Integer)), i: int, j: int) returns (m': $Mutation (Vec ($1_optional_aggregator_Integer)))
{
    var v: Vec ($1_optional_aggregator_Integer);
    v := $Dereference(m);
    if (!InRangeVec(v, i) || !InRangeVec(v, j)) {
        call $ExecFailureAbort();
        return;
    }
    m' := $UpdateMutation(m, SwapVec(v, i, j));
}

function {:inline} $1_vector_$swap'$1_optional_aggregator_Integer'(v: Vec ($1_optional_aggregator_Integer), i: int, j: int): Vec ($1_optional_aggregator_Integer) {
    SwapVec(v, i, j)
}

procedure {:inline 1} $1_vector_remove'$1_optional_aggregator_Integer'(m: $Mutation (Vec ($1_optional_aggregator_Integer)), i: int) returns (e: $1_optional_aggregator_Integer, m': $Mutation (Vec ($1_optional_aggregator_Integer)))
{
    var v: Vec ($1_optional_aggregator_Integer);

    v := $Dereference(m);

    if (!InRangeVec(v, i)) {
        call $ExecFailureAbort();
        return;
    }
    e := ReadVec(v, i);
    m' := $UpdateMutation(m, RemoveAtVec(v, i));
}

procedure {:inline 1} $1_vector_swap_remove'$1_optional_aggregator_Integer'(m: $Mutation (Vec ($1_optional_aggregator_Integer)), i: int) returns (e: $1_optional_aggregator_Integer, m': $Mutation (Vec ($1_optional_aggregator_Integer)))
{
    var len: int;
    var v: Vec ($1_optional_aggregator_Integer);

    v := $Dereference(m);
    len := LenVec(v);
    if (!InRangeVec(v, i)) {
        call $ExecFailureAbort();
        return;
    }
    e := ReadVec(v, i);
    m' := $UpdateMutation(m, RemoveVec(SwapVec(v, i, len-1)));
}

procedure {:inline 1} $1_vector_contains'$1_optional_aggregator_Integer'(v: Vec ($1_optional_aggregator_Integer), e: $1_optional_aggregator_Integer) returns (res: bool)  {
    res := $ContainsVec'$1_optional_aggregator_Integer'(v, e);
}

procedure {:inline 1}
$1_vector_index_of'$1_optional_aggregator_Integer'(v: Vec ($1_optional_aggregator_Integer), e: $1_optional_aggregator_Integer) returns (res1: bool, res2: int) {
    res2 := $IndexOfVec'$1_optional_aggregator_Integer'(v, e);
    if (res2 >= 0) {
        res1 := true;
    } else {
        res1 := false;
        res2 := 0;
    }
}


// ----------------------------------------------------------------------------------
// Native Vector implementation for element type `$1_optional_aggregator_OptionalAggregator`

// Not inlined. It appears faster this way.
function $IsEqual'vec'$1_optional_aggregator_OptionalAggregator''(v1: Vec ($1_optional_aggregator_OptionalAggregator), v2: Vec ($1_optional_aggregator_OptionalAggregator)): bool {
    LenVec(v1) == LenVec(v2) &&
    (forall i: int:: InRangeVec(v1, i) ==> $IsEqual'$1_optional_aggregator_OptionalAggregator'(ReadVec(v1, i), ReadVec(v2, i)))
}

// Not inlined.
function $IsPrefix'vec'$1_optional_aggregator_OptionalAggregator''(v: Vec ($1_optional_aggregator_OptionalAggregator), prefix: Vec ($1_optional_aggregator_OptionalAggregator)): bool {
    LenVec(v) >= LenVec(prefix) &&
    (forall i: int:: InRangeVec(prefix, i) ==> $IsEqual'$1_optional_aggregator_OptionalAggregator'(ReadVec(v, i), ReadVec(prefix, i)))
}

// Not inlined.
function $IsSuffix'vec'$1_optional_aggregator_OptionalAggregator''(v: Vec ($1_optional_aggregator_OptionalAggregator), suffix: Vec ($1_optional_aggregator_OptionalAggregator)): bool {
    LenVec(v) >= LenVec(suffix) &&
    (forall i: int:: InRangeVec(suffix, i) ==> $IsEqual'$1_optional_aggregator_OptionalAggregator'(ReadVec(v, LenVec(v) - LenVec(suffix) + i), ReadVec(suffix, i)))
}

// Not inlined.
function $IsValid'vec'$1_optional_aggregator_OptionalAggregator''(v: Vec ($1_optional_aggregator_OptionalAggregator)): bool {
    $IsValid'u64'(LenVec(v)) &&
    (forall i: int:: InRangeVec(v, i) ==> $IsValid'$1_optional_aggregator_OptionalAggregator'(ReadVec(v, i)))
}


function {:inline} $ContainsVec'$1_optional_aggregator_OptionalAggregator'(v: Vec ($1_optional_aggregator_OptionalAggregator), e: $1_optional_aggregator_OptionalAggregator): bool {
    (exists i: int :: $IsValid'u64'(i) && InRangeVec(v, i) && $IsEqual'$1_optional_aggregator_OptionalAggregator'(ReadVec(v, i), e))
}

function $IndexOfVec'$1_optional_aggregator_OptionalAggregator'(v: Vec ($1_optional_aggregator_OptionalAggregator), e: $1_optional_aggregator_OptionalAggregator): int;
axiom (forall v: Vec ($1_optional_aggregator_OptionalAggregator), e: $1_optional_aggregator_OptionalAggregator:: {$IndexOfVec'$1_optional_aggregator_OptionalAggregator'(v, e)}
    (var i := $IndexOfVec'$1_optional_aggregator_OptionalAggregator'(v, e);
     if (!$ContainsVec'$1_optional_aggregator_OptionalAggregator'(v, e)) then i == -1
     else $IsValid'u64'(i) && InRangeVec(v, i) && $IsEqual'$1_optional_aggregator_OptionalAggregator'(ReadVec(v, i), e) &&
        (forall j: int :: $IsValid'u64'(j) && j >= 0 && j < i ==> !$IsEqual'$1_optional_aggregator_OptionalAggregator'(ReadVec(v, j), e))));


function {:inline} $RangeVec'$1_optional_aggregator_OptionalAggregator'(v: Vec ($1_optional_aggregator_OptionalAggregator)): $Range {
    $Range(0, LenVec(v))
}


function {:inline} $EmptyVec'$1_optional_aggregator_OptionalAggregator'(): Vec ($1_optional_aggregator_OptionalAggregator) {
    EmptyVec()
}

procedure {:inline 1} $1_vector_empty'$1_optional_aggregator_OptionalAggregator'() returns (v: Vec ($1_optional_aggregator_OptionalAggregator)) {
    v := EmptyVec();
}

function {:inline} $1_vector_$empty'$1_optional_aggregator_OptionalAggregator'(): Vec ($1_optional_aggregator_OptionalAggregator) {
    EmptyVec()
}

procedure {:inline 1} $1_vector_is_empty'$1_optional_aggregator_OptionalAggregator'(v: Vec ($1_optional_aggregator_OptionalAggregator)) returns (b: bool) {
    b := IsEmptyVec(v);
}

procedure {:inline 1} $1_vector_push_back'$1_optional_aggregator_OptionalAggregator'(m: $Mutation (Vec ($1_optional_aggregator_OptionalAggregator)), val: $1_optional_aggregator_OptionalAggregator) returns (m': $Mutation (Vec ($1_optional_aggregator_OptionalAggregator))) {
    m' := $UpdateMutation(m, ExtendVec($Dereference(m), val));
}

function {:inline} $1_vector_$push_back'$1_optional_aggregator_OptionalAggregator'(v: Vec ($1_optional_aggregator_OptionalAggregator), val: $1_optional_aggregator_OptionalAggregator): Vec ($1_optional_aggregator_OptionalAggregator) {
    ExtendVec(v, val)
}

procedure {:inline 1} $1_vector_pop_back'$1_optional_aggregator_OptionalAggregator'(m: $Mutation (Vec ($1_optional_aggregator_OptionalAggregator))) returns (e: $1_optional_aggregator_OptionalAggregator, m': $Mutation (Vec ($1_optional_aggregator_OptionalAggregator))) {
    var v: Vec ($1_optional_aggregator_OptionalAggregator);
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

procedure {:inline 1} $1_vector_append'$1_optional_aggregator_OptionalAggregator'(m: $Mutation (Vec ($1_optional_aggregator_OptionalAggregator)), other: Vec ($1_optional_aggregator_OptionalAggregator)) returns (m': $Mutation (Vec ($1_optional_aggregator_OptionalAggregator))) {
    m' := $UpdateMutation(m, ConcatVec($Dereference(m), other));
}

procedure {:inline 1} $1_vector_reverse'$1_optional_aggregator_OptionalAggregator'(m: $Mutation (Vec ($1_optional_aggregator_OptionalAggregator))) returns (m': $Mutation (Vec ($1_optional_aggregator_OptionalAggregator))) {
    m' := $UpdateMutation(m, ReverseVec($Dereference(m)));
}

procedure {:inline 1} $1_vector_reverse_append'$1_optional_aggregator_OptionalAggregator'(m: $Mutation (Vec ($1_optional_aggregator_OptionalAggregator)), other: Vec ($1_optional_aggregator_OptionalAggregator)) returns (m': $Mutation (Vec ($1_optional_aggregator_OptionalAggregator))) {
    m' := $UpdateMutation(m, ConcatVec($Dereference(m), ReverseVec(other)));
}

procedure {:inline 1} $1_vector_trim_reverse'$1_optional_aggregator_OptionalAggregator'(m: $Mutation (Vec ($1_optional_aggregator_OptionalAggregator)), new_len: int) returns (v: (Vec ($1_optional_aggregator_OptionalAggregator)), m': $Mutation (Vec ($1_optional_aggregator_OptionalAggregator))) {
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

procedure {:inline 1} $1_vector_trim'$1_optional_aggregator_OptionalAggregator'(m: $Mutation (Vec ($1_optional_aggregator_OptionalAggregator)), new_len: int) returns (v: (Vec ($1_optional_aggregator_OptionalAggregator)), m': $Mutation (Vec ($1_optional_aggregator_OptionalAggregator))) {
    var len: int;
    v := $Dereference(m);
    if (LenVec(v) < new_len) {
        call $ExecFailureAbort();
        return;
    }
    v := SliceVec(v, new_len, LenVec(v));
    m' := $UpdateMutation(m, SliceVec($Dereference(m), 0, new_len));
}

procedure {:inline 1} $1_vector_reverse_slice'$1_optional_aggregator_OptionalAggregator'(m: $Mutation (Vec ($1_optional_aggregator_OptionalAggregator)), left: int, right: int) returns (m': $Mutation (Vec ($1_optional_aggregator_OptionalAggregator))) {
    var left_vec: Vec ($1_optional_aggregator_OptionalAggregator);
    var mid_vec: Vec ($1_optional_aggregator_OptionalAggregator);
    var right_vec: Vec ($1_optional_aggregator_OptionalAggregator);
    var v: Vec ($1_optional_aggregator_OptionalAggregator);
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

procedure {:inline 1} $1_vector_rotate'$1_optional_aggregator_OptionalAggregator'(m: $Mutation (Vec ($1_optional_aggregator_OptionalAggregator)), rot: int) returns (n: int, m': $Mutation (Vec ($1_optional_aggregator_OptionalAggregator))) {
    var v: Vec ($1_optional_aggregator_OptionalAggregator);
    var len: int;
    var left_vec: Vec ($1_optional_aggregator_OptionalAggregator);
    var right_vec: Vec ($1_optional_aggregator_OptionalAggregator);
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

procedure {:inline 1} $1_vector_rotate_slice'$1_optional_aggregator_OptionalAggregator'(m: $Mutation (Vec ($1_optional_aggregator_OptionalAggregator)), left: int, rot: int, right: int) returns (n: int, m': $Mutation (Vec ($1_optional_aggregator_OptionalAggregator))) {
    var left_vec: Vec ($1_optional_aggregator_OptionalAggregator);
    var mid_vec: Vec ($1_optional_aggregator_OptionalAggregator);
    var right_vec: Vec ($1_optional_aggregator_OptionalAggregator);
    var mid_left_vec: Vec ($1_optional_aggregator_OptionalAggregator);
    var mid_right_vec: Vec ($1_optional_aggregator_OptionalAggregator);
    var v: Vec ($1_optional_aggregator_OptionalAggregator);
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

procedure {:inline 1} $1_vector_insert'$1_optional_aggregator_OptionalAggregator'(m: $Mutation (Vec ($1_optional_aggregator_OptionalAggregator)), i: int, e: $1_optional_aggregator_OptionalAggregator) returns (m': $Mutation (Vec ($1_optional_aggregator_OptionalAggregator))) {
    var left_vec: Vec ($1_optional_aggregator_OptionalAggregator);
    var right_vec: Vec ($1_optional_aggregator_OptionalAggregator);
    var v: Vec ($1_optional_aggregator_OptionalAggregator);
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

procedure {:inline 1} $1_vector_length'$1_optional_aggregator_OptionalAggregator'(v: Vec ($1_optional_aggregator_OptionalAggregator)) returns (l: int) {
    l := LenVec(v);
}

function {:inline} $1_vector_$length'$1_optional_aggregator_OptionalAggregator'(v: Vec ($1_optional_aggregator_OptionalAggregator)): int {
    LenVec(v)
}

procedure {:inline 1} $1_vector_borrow'$1_optional_aggregator_OptionalAggregator'(v: Vec ($1_optional_aggregator_OptionalAggregator), i: int) returns (dst: $1_optional_aggregator_OptionalAggregator) {
    if (!InRangeVec(v, i)) {
        call $ExecFailureAbort();
        return;
    }
    dst := ReadVec(v, i);
}

function {:inline} $1_vector_$borrow'$1_optional_aggregator_OptionalAggregator'(v: Vec ($1_optional_aggregator_OptionalAggregator), i: int): $1_optional_aggregator_OptionalAggregator {
    ReadVec(v, i)
}

procedure {:inline 1} $1_vector_borrow_mut'$1_optional_aggregator_OptionalAggregator'(m: $Mutation (Vec ($1_optional_aggregator_OptionalAggregator)), index: int)
returns (dst: $Mutation ($1_optional_aggregator_OptionalAggregator), m': $Mutation (Vec ($1_optional_aggregator_OptionalAggregator)))
{
    var v: Vec ($1_optional_aggregator_OptionalAggregator);
    v := $Dereference(m);
    if (!InRangeVec(v, index)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Mutation(l#$Mutation(m), ExtendVec(p#$Mutation(m), index), ReadVec(v, index));
    m' := m;
}

function {:inline} $1_vector_$borrow_mut'$1_optional_aggregator_OptionalAggregator'(v: Vec ($1_optional_aggregator_OptionalAggregator), i: int): $1_optional_aggregator_OptionalAggregator {
    ReadVec(v, i)
}

procedure {:inline 1} $1_vector_destroy_empty'$1_optional_aggregator_OptionalAggregator'(v: Vec ($1_optional_aggregator_OptionalAggregator)) {
    if (!IsEmptyVec(v)) {
      call $ExecFailureAbort();
    }
}

procedure {:inline 1} $1_vector_swap'$1_optional_aggregator_OptionalAggregator'(m: $Mutation (Vec ($1_optional_aggregator_OptionalAggregator)), i: int, j: int) returns (m': $Mutation (Vec ($1_optional_aggregator_OptionalAggregator)))
{
    var v: Vec ($1_optional_aggregator_OptionalAggregator);
    v := $Dereference(m);
    if (!InRangeVec(v, i) || !InRangeVec(v, j)) {
        call $ExecFailureAbort();
        return;
    }
    m' := $UpdateMutation(m, SwapVec(v, i, j));
}

function {:inline} $1_vector_$swap'$1_optional_aggregator_OptionalAggregator'(v: Vec ($1_optional_aggregator_OptionalAggregator), i: int, j: int): Vec ($1_optional_aggregator_OptionalAggregator) {
    SwapVec(v, i, j)
}

procedure {:inline 1} $1_vector_remove'$1_optional_aggregator_OptionalAggregator'(m: $Mutation (Vec ($1_optional_aggregator_OptionalAggregator)), i: int) returns (e: $1_optional_aggregator_OptionalAggregator, m': $Mutation (Vec ($1_optional_aggregator_OptionalAggregator)))
{
    var v: Vec ($1_optional_aggregator_OptionalAggregator);

    v := $Dereference(m);

    if (!InRangeVec(v, i)) {
        call $ExecFailureAbort();
        return;
    }
    e := ReadVec(v, i);
    m' := $UpdateMutation(m, RemoveAtVec(v, i));
}

procedure {:inline 1} $1_vector_swap_remove'$1_optional_aggregator_OptionalAggregator'(m: $Mutation (Vec ($1_optional_aggregator_OptionalAggregator)), i: int) returns (e: $1_optional_aggregator_OptionalAggregator, m': $Mutation (Vec ($1_optional_aggregator_OptionalAggregator)))
{
    var len: int;
    var v: Vec ($1_optional_aggregator_OptionalAggregator);

    v := $Dereference(m);
    len := LenVec(v);
    if (!InRangeVec(v, i)) {
        call $ExecFailureAbort();
        return;
    }
    e := ReadVec(v, i);
    m' := $UpdateMutation(m, RemoveVec(SwapVec(v, i, len-1)));
}

procedure {:inline 1} $1_vector_contains'$1_optional_aggregator_OptionalAggregator'(v: Vec ($1_optional_aggregator_OptionalAggregator), e: $1_optional_aggregator_OptionalAggregator) returns (res: bool)  {
    res := $ContainsVec'$1_optional_aggregator_OptionalAggregator'(v, e);
}

procedure {:inline 1}
$1_vector_index_of'$1_optional_aggregator_OptionalAggregator'(v: Vec ($1_optional_aggregator_OptionalAggregator), e: $1_optional_aggregator_OptionalAggregator) returns (res1: bool, res2: int) {
    res2 := $IndexOfVec'$1_optional_aggregator_OptionalAggregator'(v, e);
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
// Native Table implementation for type `(address,$1_staking_contract_StakingContract)`

function $IsEqual'$1_simple_map_SimpleMap'address_$1_staking_contract_StakingContract''(t1: Table int ($1_staking_contract_StakingContract), t2: Table int ($1_staking_contract_StakingContract)): bool {
    LenTable(t1) == LenTable(t2) &&
    (forall k: int :: ContainsTable(t1, k) <==> ContainsTable(t2, k)) &&
    (forall k: int :: ContainsTable(t1, k) ==> GetTable(t1, k) == GetTable(t2, k)) &&
    (forall k: int :: ContainsTable(t2, k) ==> GetTable(t1, k) == GetTable(t2, k))
}

// Not inlined.
function $IsValid'$1_simple_map_SimpleMap'address_$1_staking_contract_StakingContract''(t: Table int ($1_staking_contract_StakingContract)): bool {
    $IsValid'u64'(LenTable(t)) &&
    (forall i: int:: ContainsTable(t, i) ==> $IsValid'$1_staking_contract_StakingContract'(GetTable(t, i)))
}
procedure {:inline 2} $1_simple_map_create'address_$1_staking_contract_StakingContract'() returns (v: Table int ($1_staking_contract_StakingContract)) {
    v := EmptyTable();
}
procedure {:inline 2} $1_simple_map_destroy_empty'address_$1_staking_contract_StakingContract'(t: Table int ($1_staking_contract_StakingContract)) {
    if (LenTable(t) != 0) {
        call $Abort($StdError(1/*INVALID_STATE*/, 102/*ENOT_EMPTY*/));
    }
}
procedure {:inline 2} $1_simple_map_length'address_$1_staking_contract_StakingContract'(t: (Table int ($1_staking_contract_StakingContract))) returns (l: int) {
    l := LenTable(t);
}
procedure {:inline 2} $1_simple_map_contains_key'address_$1_staking_contract_StakingContract'(t: (Table int ($1_staking_contract_StakingContract)), k: int) returns (r: bool) {
    r := ContainsTable(t, $EncodeKey'address'(k));
}
procedure {:inline 2} $1_simple_map_add'address_$1_staking_contract_StakingContract'(m: $Mutation (Table int ($1_staking_contract_StakingContract)), k: int, v: $1_staking_contract_StakingContract) returns (m': $Mutation(Table int ($1_staking_contract_StakingContract))) {
    var enc_k: int;
    var t: Table int ($1_staking_contract_StakingContract);
    enc_k := $EncodeKey'address'(k);
    t := $Dereference(m);
    if (ContainsTable(t, enc_k)) {
        call $Abort($StdError(7/*INVALID_ARGUMENTS*/, 100/*EALREADY_EXISTS*/));
    } else {
        m' := $UpdateMutation(m, AddTable(t, enc_k, v));
    }
}
procedure {:inline 2} $1_simple_map_remove'address_$1_staking_contract_StakingContract'(m: $Mutation (Table int ($1_staking_contract_StakingContract)), k: int)
returns (k': int, v: $1_staking_contract_StakingContract, m': $Mutation(Table int ($1_staking_contract_StakingContract))) {
    var enc_k: int;
    var t: Table int ($1_staking_contract_StakingContract);
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
procedure {:inline 2} $1_simple_map_borrow'address_$1_staking_contract_StakingContract'(t: Table int ($1_staking_contract_StakingContract), k: int) returns (v: $1_staking_contract_StakingContract) {
    var enc_k: int;
    enc_k := $EncodeKey'address'(k);
    if (!ContainsTable(t, enc_k)) {
        call $Abort($StdError(7/*INVALID_ARGUMENTS*/, 101/*ENOT_FOUND*/));
    } else {
        v := GetTable(t, $EncodeKey'address'(k));
    }
}
procedure {:inline 2} $1_simple_map_borrow_mut'address_$1_staking_contract_StakingContract'(m: $Mutation (Table int ($1_staking_contract_StakingContract)), k: int)
returns (dst: $Mutation ($1_staking_contract_StakingContract), m': $Mutation (Table int ($1_staking_contract_StakingContract))) {
    var enc_k: int;
    var t: Table int ($1_staking_contract_StakingContract);
    enc_k := $EncodeKey'address'(k);
    t := $Dereference(m);
    if (!ContainsTable(t, enc_k)) {
        call $Abort($StdError(7/*INVALID_ARGUMENTS*/, 101/*ENOT_FOUND*/));
    } else {
        dst := $Mutation(l#$Mutation(m), ExtendVec(p#$Mutation(m), enc_k), GetTable(t, enc_k));
        m' := m;
    }
}
function {:inline} $1_simple_map_spec_len'address_$1_staking_contract_StakingContract'(t: (Table int ($1_staking_contract_StakingContract))): int {
    LenTable(t)
}
function {:inline} $1_simple_map_spec_contains_key'address_$1_staking_contract_StakingContract'(t: (Table int ($1_staking_contract_StakingContract)), k: int): bool {
    ContainsTable(t, $EncodeKey'address'(k))
}
function {:inline} $1_simple_map_spec_set'address_$1_staking_contract_StakingContract'(t: Table int ($1_staking_contract_StakingContract), k: int, v: $1_staking_contract_StakingContract): Table int ($1_staking_contract_StakingContract) {
    (var enc_k := $EncodeKey'address'(k);
    if (ContainsTable(t, enc_k)) then
        UpdateTable(t, enc_k, v)
    else
        AddTable(t, enc_k, v))
}
function {:inline} $1_simple_map_spec_remove'address_$1_staking_contract_StakingContract'(t: Table int ($1_staking_contract_StakingContract), k: int): Table int ($1_staking_contract_StakingContract) {
    RemoveTable(t, $EncodeKey'address'(k))
}
function {:inline} $1_simple_map_spec_get'address_$1_staking_contract_StakingContract'(t: Table int ($1_staking_contract_StakingContract), k: int): $1_staking_contract_StakingContract {
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

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:14:9+116, instance <vector<u8>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''($1_from_bcs_deserialize'vec'u8''(b1), $1_from_bcs_deserialize'vec'u8''(b2)) ==> $IsEqual'vec'u8''(b1, b2))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:14:9+116, instance <vector<address>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'address''($1_from_bcs_deserialize'vec'address''(b1), $1_from_bcs_deserialize'vec'address''(b2)) ==> $IsEqual'vec'u8''(b1, b2))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:14:9+116, instance <vector<aggregator::Aggregator>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'$1_aggregator_Aggregator''($1_from_bcs_deserialize'vec'$1_aggregator_Aggregator''(b1), $1_from_bcs_deserialize'vec'$1_aggregator_Aggregator''(b2)) ==> $IsEqual'vec'u8''(b1, b2))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:14:9+116, instance <vector<optional_aggregator::Integer>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'$1_optional_aggregator_Integer''($1_from_bcs_deserialize'vec'$1_optional_aggregator_Integer''(b1), $1_from_bcs_deserialize'vec'$1_optional_aggregator_Integer''(b2)) ==> $IsEqual'vec'u8''(b1, b2))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:14:9+116, instance <vector<optional_aggregator::OptionalAggregator>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'$1_optional_aggregator_OptionalAggregator''($1_from_bcs_deserialize'vec'$1_optional_aggregator_OptionalAggregator''(b1), $1_from_bcs_deserialize'vec'$1_optional_aggregator_OptionalAggregator''(b2)) ==> $IsEqual'vec'u8''(b1, b2))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:14:9+116, instance <vector<stake::IndividualValidatorPerformance>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'$1_stake_IndividualValidatorPerformance''($1_from_bcs_deserialize'vec'$1_stake_IndividualValidatorPerformance''(b1), $1_from_bcs_deserialize'vec'$1_stake_IndividualValidatorPerformance''(b2)) ==> $IsEqual'vec'u8''(b1, b2))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:14:9+116, instance <vector<stake::ValidatorInfo>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'$1_stake_ValidatorInfo''($1_from_bcs_deserialize'vec'$1_stake_ValidatorInfo''(b1), $1_from_bcs_deserialize'vec'$1_stake_ValidatorInfo''(b2)) ==> $IsEqual'vec'u8''(b1, b2))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:14:9+116, instance <vector<#0>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'#0''($1_from_bcs_deserialize'vec'#0''(b1), $1_from_bcs_deserialize'vec'#0''(b2)) ==> $IsEqual'vec'u8''(b1, b2))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:14:9+116, instance <option::Option<aggregator::Aggregator>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'$1_option_Option'$1_aggregator_Aggregator''($1_from_bcs_deserialize'$1_option_Option'$1_aggregator_Aggregator''(b1), $1_from_bcs_deserialize'$1_option_Option'$1_aggregator_Aggregator''(b2)) ==> $IsEqual'vec'u8''(b1, b2))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:14:9+116, instance <option::Option<optional_aggregator::Integer>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'$1_option_Option'$1_optional_aggregator_Integer''($1_from_bcs_deserialize'$1_option_Option'$1_optional_aggregator_Integer''(b1), $1_from_bcs_deserialize'$1_option_Option'$1_optional_aggregator_Integer''(b2)) ==> $IsEqual'vec'u8''(b1, b2))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:14:9+116, instance <option::Option<optional_aggregator::OptionalAggregator>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'$1_option_Option'$1_optional_aggregator_OptionalAggregator''($1_from_bcs_deserialize'$1_option_Option'$1_optional_aggregator_OptionalAggregator''(b1), $1_from_bcs_deserialize'$1_option_Option'$1_optional_aggregator_OptionalAggregator''(b2)) ==> $IsEqual'vec'u8''(b1, b2))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:14:9+116, instance <string::String>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'$1_string_String'($1_from_bcs_deserialize'$1_string_String'(b1), $1_from_bcs_deserialize'$1_string_String'(b2)) ==> $IsEqual'vec'u8''(b1, b2))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:14:9+116, instance <type_info::TypeInfo>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'$1_type_info_TypeInfo'($1_from_bcs_deserialize'$1_type_info_TypeInfo'(b1), $1_from_bcs_deserialize'$1_type_info_TypeInfo'(b2)) ==> $IsEqual'vec'u8''(b1, b2))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:14:9+116, instance <guid::GUID>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'$1_guid_GUID'($1_from_bcs_deserialize'$1_guid_GUID'(b1), $1_from_bcs_deserialize'$1_guid_GUID'(b2)) ==> $IsEqual'vec'u8''(b1, b2))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:14:9+116, instance <guid::ID>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'$1_guid_ID'($1_from_bcs_deserialize'$1_guid_ID'(b1), $1_from_bcs_deserialize'$1_guid_ID'(b2)) ==> $IsEqual'vec'u8''(b1, b2))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:14:9+116, instance <event::EventHandle<stake::AddStakeEvent>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'$1_event_EventHandle'$1_stake_AddStakeEvent''($1_from_bcs_deserialize'$1_event_EventHandle'$1_stake_AddStakeEvent''(b1), $1_from_bcs_deserialize'$1_event_EventHandle'$1_stake_AddStakeEvent''(b2)) ==> $IsEqual'vec'u8''(b1, b2))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:14:9+116, instance <event::EventHandle<stake::DistributeRewardsEvent>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'$1_event_EventHandle'$1_stake_DistributeRewardsEvent''($1_from_bcs_deserialize'$1_event_EventHandle'$1_stake_DistributeRewardsEvent''(b1), $1_from_bcs_deserialize'$1_event_EventHandle'$1_stake_DistributeRewardsEvent''(b2)) ==> $IsEqual'vec'u8''(b1, b2))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:14:9+116, instance <event::EventHandle<stake::IncreaseLockupEvent>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'$1_event_EventHandle'$1_stake_IncreaseLockupEvent''($1_from_bcs_deserialize'$1_event_EventHandle'$1_stake_IncreaseLockupEvent''(b1), $1_from_bcs_deserialize'$1_event_EventHandle'$1_stake_IncreaseLockupEvent''(b2)) ==> $IsEqual'vec'u8''(b1, b2))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:14:9+116, instance <event::EventHandle<stake::JoinValidatorSetEvent>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'$1_event_EventHandle'$1_stake_JoinValidatorSetEvent''($1_from_bcs_deserialize'$1_event_EventHandle'$1_stake_JoinValidatorSetEvent''(b1), $1_from_bcs_deserialize'$1_event_EventHandle'$1_stake_JoinValidatorSetEvent''(b2)) ==> $IsEqual'vec'u8''(b1, b2))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:14:9+116, instance <event::EventHandle<stake::LeaveValidatorSetEvent>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'$1_event_EventHandle'$1_stake_LeaveValidatorSetEvent''($1_from_bcs_deserialize'$1_event_EventHandle'$1_stake_LeaveValidatorSetEvent''(b1), $1_from_bcs_deserialize'$1_event_EventHandle'$1_stake_LeaveValidatorSetEvent''(b2)) ==> $IsEqual'vec'u8''(b1, b2))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:14:9+116, instance <event::EventHandle<stake::ReactivateStakeEvent>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'$1_event_EventHandle'$1_stake_ReactivateStakeEvent''($1_from_bcs_deserialize'$1_event_EventHandle'$1_stake_ReactivateStakeEvent''(b1), $1_from_bcs_deserialize'$1_event_EventHandle'$1_stake_ReactivateStakeEvent''(b2)) ==> $IsEqual'vec'u8''(b1, b2))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:14:9+116, instance <event::EventHandle<stake::RegisterValidatorCandidateEvent>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'$1_event_EventHandle'$1_stake_RegisterValidatorCandidateEvent''($1_from_bcs_deserialize'$1_event_EventHandle'$1_stake_RegisterValidatorCandidateEvent''(b1), $1_from_bcs_deserialize'$1_event_EventHandle'$1_stake_RegisterValidatorCandidateEvent''(b2)) ==> $IsEqual'vec'u8''(b1, b2))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:14:9+116, instance <event::EventHandle<stake::RotateConsensusKeyEvent>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'$1_event_EventHandle'$1_stake_RotateConsensusKeyEvent''($1_from_bcs_deserialize'$1_event_EventHandle'$1_stake_RotateConsensusKeyEvent''(b1), $1_from_bcs_deserialize'$1_event_EventHandle'$1_stake_RotateConsensusKeyEvent''(b2)) ==> $IsEqual'vec'u8''(b1, b2))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:14:9+116, instance <event::EventHandle<stake::SetOperatorEvent>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'$1_event_EventHandle'$1_stake_SetOperatorEvent''($1_from_bcs_deserialize'$1_event_EventHandle'$1_stake_SetOperatorEvent''(b1), $1_from_bcs_deserialize'$1_event_EventHandle'$1_stake_SetOperatorEvent''(b2)) ==> $IsEqual'vec'u8''(b1, b2))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:14:9+116, instance <event::EventHandle<stake::UnlockStakeEvent>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'$1_event_EventHandle'$1_stake_UnlockStakeEvent''($1_from_bcs_deserialize'$1_event_EventHandle'$1_stake_UnlockStakeEvent''(b1), $1_from_bcs_deserialize'$1_event_EventHandle'$1_stake_UnlockStakeEvent''(b2)) ==> $IsEqual'vec'u8''(b1, b2))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:14:9+116, instance <event::EventHandle<stake::UpdateNetworkAndFullnodeAddressesEvent>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'$1_event_EventHandle'$1_stake_UpdateNetworkAndFullnodeAddressesEvent''($1_from_bcs_deserialize'$1_event_EventHandle'$1_stake_UpdateNetworkAndFullnodeAddressesEvent''(b1), $1_from_bcs_deserialize'$1_event_EventHandle'$1_stake_UpdateNetworkAndFullnodeAddressesEvent''(b2)) ==> $IsEqual'vec'u8''(b1, b2))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:14:9+116, instance <event::EventHandle<stake::WithdrawStakeEvent>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'$1_event_EventHandle'$1_stake_WithdrawStakeEvent''($1_from_bcs_deserialize'$1_event_EventHandle'$1_stake_WithdrawStakeEvent''(b1), $1_from_bcs_deserialize'$1_event_EventHandle'$1_stake_WithdrawStakeEvent''(b2)) ==> $IsEqual'vec'u8''(b1, b2))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:14:9+116, instance <event::EventHandle<staking_contract::AddStakeEvent>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'$1_event_EventHandle'$1_staking_contract_AddStakeEvent''($1_from_bcs_deserialize'$1_event_EventHandle'$1_staking_contract_AddStakeEvent''(b1), $1_from_bcs_deserialize'$1_event_EventHandle'$1_staking_contract_AddStakeEvent''(b2)) ==> $IsEqual'vec'u8''(b1, b2))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:14:9+116, instance <event::EventHandle<staking_contract::UnlockStakeEvent>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'$1_event_EventHandle'$1_staking_contract_UnlockStakeEvent''($1_from_bcs_deserialize'$1_event_EventHandle'$1_staking_contract_UnlockStakeEvent''(b1), $1_from_bcs_deserialize'$1_event_EventHandle'$1_staking_contract_UnlockStakeEvent''(b2)) ==> $IsEqual'vec'u8''(b1, b2))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:14:9+116, instance <event::EventHandle<staking_contract::AddDistributionEvent>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'$1_event_EventHandle'$1_staking_contract_AddDistributionEvent''($1_from_bcs_deserialize'$1_event_EventHandle'$1_staking_contract_AddDistributionEvent''(b1), $1_from_bcs_deserialize'$1_event_EventHandle'$1_staking_contract_AddDistributionEvent''(b2)) ==> $IsEqual'vec'u8''(b1, b2))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:14:9+116, instance <event::EventHandle<staking_contract::CreateStakingContractEvent>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'$1_event_EventHandle'$1_staking_contract_CreateStakingContractEvent''($1_from_bcs_deserialize'$1_event_EventHandle'$1_staking_contract_CreateStakingContractEvent''(b1), $1_from_bcs_deserialize'$1_event_EventHandle'$1_staking_contract_CreateStakingContractEvent''(b2)) ==> $IsEqual'vec'u8''(b1, b2))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:14:9+116, instance <event::EventHandle<staking_contract::DistributeEvent>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'$1_event_EventHandle'$1_staking_contract_DistributeEvent''($1_from_bcs_deserialize'$1_event_EventHandle'$1_staking_contract_DistributeEvent''(b1), $1_from_bcs_deserialize'$1_event_EventHandle'$1_staking_contract_DistributeEvent''(b2)) ==> $IsEqual'vec'u8''(b1, b2))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:14:9+116, instance <event::EventHandle<staking_contract::RequestCommissionEvent>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'$1_event_EventHandle'$1_staking_contract_RequestCommissionEvent''($1_from_bcs_deserialize'$1_event_EventHandle'$1_staking_contract_RequestCommissionEvent''(b1), $1_from_bcs_deserialize'$1_event_EventHandle'$1_staking_contract_RequestCommissionEvent''(b2)) ==> $IsEqual'vec'u8''(b1, b2))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:14:9+116, instance <event::EventHandle<staking_contract::ResetLockupEvent>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'$1_event_EventHandle'$1_staking_contract_ResetLockupEvent''($1_from_bcs_deserialize'$1_event_EventHandle'$1_staking_contract_ResetLockupEvent''(b1), $1_from_bcs_deserialize'$1_event_EventHandle'$1_staking_contract_ResetLockupEvent''(b2)) ==> $IsEqual'vec'u8''(b1, b2))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:14:9+116, instance <event::EventHandle<staking_contract::SwitchOperatorEvent>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'$1_event_EventHandle'$1_staking_contract_SwitchOperatorEvent''($1_from_bcs_deserialize'$1_event_EventHandle'$1_staking_contract_SwitchOperatorEvent''(b1), $1_from_bcs_deserialize'$1_event_EventHandle'$1_staking_contract_SwitchOperatorEvent''(b2)) ==> $IsEqual'vec'u8''(b1, b2))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:14:9+116, instance <event::EventHandle<staking_contract::UpdateVoterEvent>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'$1_event_EventHandle'$1_staking_contract_UpdateVoterEvent''($1_from_bcs_deserialize'$1_event_EventHandle'$1_staking_contract_UpdateVoterEvent''(b1), $1_from_bcs_deserialize'$1_event_EventHandle'$1_staking_contract_UpdateVoterEvent''(b2)) ==> $IsEqual'vec'u8''(b1, b2))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:14:9+116, instance <account::SignerCapability>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'$1_account_SignerCapability'($1_from_bcs_deserialize'$1_account_SignerCapability'(b1), $1_from_bcs_deserialize'$1_account_SignerCapability'(b2)) ==> $IsEqual'vec'u8''(b1, b2))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:14:9+116, instance <aggregator::Aggregator>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'$1_aggregator_Aggregator'($1_from_bcs_deserialize'$1_aggregator_Aggregator'(b1), $1_from_bcs_deserialize'$1_aggregator_Aggregator'(b2)) ==> $IsEqual'vec'u8''(b1, b2))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:14:9+116, instance <optional_aggregator::Integer>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'$1_optional_aggregator_Integer'($1_from_bcs_deserialize'$1_optional_aggregator_Integer'(b1), $1_from_bcs_deserialize'$1_optional_aggregator_Integer'(b2)) ==> $IsEqual'vec'u8''(b1, b2))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:14:9+116, instance <optional_aggregator::OptionalAggregator>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'$1_optional_aggregator_OptionalAggregator'($1_from_bcs_deserialize'$1_optional_aggregator_OptionalAggregator'(b1), $1_from_bcs_deserialize'$1_optional_aggregator_OptionalAggregator'(b2)) ==> $IsEqual'vec'u8''(b1, b2))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:14:9+116, instance <coin::Coin<aptos_coin::AptosCoin>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'$1_coin_Coin'$1_aptos_coin_AptosCoin''($1_from_bcs_deserialize'$1_coin_Coin'$1_aptos_coin_AptosCoin''(b1), $1_from_bcs_deserialize'$1_coin_Coin'$1_aptos_coin_AptosCoin''(b2)) ==> $IsEqual'vec'u8''(b1, b2))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:14:9+116, instance <coin::CoinInfo<aptos_coin::AptosCoin>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'$1_coin_CoinInfo'$1_aptos_coin_AptosCoin''($1_from_bcs_deserialize'$1_coin_CoinInfo'$1_aptos_coin_AptosCoin''(b1), $1_from_bcs_deserialize'$1_coin_CoinInfo'$1_aptos_coin_AptosCoin''(b2)) ==> $IsEqual'vec'u8''(b1, b2))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:14:9+116, instance <coin::Ghost$supply<aptos_coin::AptosCoin>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'$1_coin_Ghost$supply'$1_aptos_coin_AptosCoin''($1_from_bcs_deserialize'$1_coin_Ghost$supply'$1_aptos_coin_AptosCoin''(b1), $1_from_bcs_deserialize'$1_coin_Ghost$supply'$1_aptos_coin_AptosCoin''(b2)) ==> $IsEqual'vec'u8''(b1, b2))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:14:9+116, instance <coin::Ghost$aggregate_supply<aptos_coin::AptosCoin>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'$1_coin_Ghost$aggregate_supply'$1_aptos_coin_AptosCoin''($1_from_bcs_deserialize'$1_coin_Ghost$aggregate_supply'$1_aptos_coin_AptosCoin''(b1), $1_from_bcs_deserialize'$1_coin_Ghost$aggregate_supply'$1_aptos_coin_AptosCoin''(b2)) ==> $IsEqual'vec'u8''(b1, b2))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:14:9+116, instance <aptos_coin::AptosCoin>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'$1_aptos_coin_AptosCoin'($1_from_bcs_deserialize'$1_aptos_coin_AptosCoin'(b1), $1_from_bcs_deserialize'$1_aptos_coin_AptosCoin'(b2)) ==> $IsEqual'vec'u8''(b1, b2))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:14:9+116, instance <simple_map::SimpleMap<address, u64>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'$1_simple_map_SimpleMap'address_u64''($1_from_bcs_deserialize'$1_simple_map_SimpleMap'address_u64''(b1), $1_from_bcs_deserialize'$1_simple_map_SimpleMap'address_u64''(b2)) ==> $IsEqual'vec'u8''(b1, b2))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:14:9+116, instance <simple_map::SimpleMap<address, staking_contract::StakingContract>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'$1_simple_map_SimpleMap'address_$1_staking_contract_StakingContract''($1_from_bcs_deserialize'$1_simple_map_SimpleMap'address_$1_staking_contract_StakingContract''(b1), $1_from_bcs_deserialize'$1_simple_map_SimpleMap'address_$1_staking_contract_StakingContract''(b2)) ==> $IsEqual'vec'u8''(b1, b2))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:14:9+116, instance <stake::OwnerCapability>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'$1_stake_OwnerCapability'($1_from_bcs_deserialize'$1_stake_OwnerCapability'(b1), $1_from_bcs_deserialize'$1_stake_OwnerCapability'(b2)) ==> $IsEqual'vec'u8''(b1, b2))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:14:9+116, instance <stake::StakePool>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'$1_stake_StakePool'($1_from_bcs_deserialize'$1_stake_StakePool'(b1), $1_from_bcs_deserialize'$1_stake_StakePool'(b2)) ==> $IsEqual'vec'u8''(b1, b2))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:14:9+116, instance <stake::ValidatorConfig>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'$1_stake_ValidatorConfig'($1_from_bcs_deserialize'$1_stake_ValidatorConfig'(b1), $1_from_bcs_deserialize'$1_stake_ValidatorConfig'(b2)) ==> $IsEqual'vec'u8''(b1, b2))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:14:9+116, instance <stake::ValidatorPerformance>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'$1_stake_ValidatorPerformance'($1_from_bcs_deserialize'$1_stake_ValidatorPerformance'(b1), $1_from_bcs_deserialize'$1_stake_ValidatorPerformance'(b2)) ==> $IsEqual'vec'u8''(b1, b2))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:14:9+116, instance <stake::ValidatorSet>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'$1_stake_ValidatorSet'($1_from_bcs_deserialize'$1_stake_ValidatorSet'(b1), $1_from_bcs_deserialize'$1_stake_ValidatorSet'(b2)) ==> $IsEqual'vec'u8''(b1, b2))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:14:9+116, instance <pool_u64::Pool>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'$1_pool_u64_Pool'($1_from_bcs_deserialize'$1_pool_u64_Pool'(b1), $1_from_bcs_deserialize'$1_pool_u64_Pool'(b2)) ==> $IsEqual'vec'u8''(b1, b2))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:14:9+116, instance <staking_contract::StakingContract>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'$1_staking_contract_StakingContract'($1_from_bcs_deserialize'$1_staking_contract_StakingContract'(b1), $1_from_bcs_deserialize'$1_staking_contract_StakingContract'(b2)) ==> $IsEqual'vec'u8''(b1, b2))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:14:9+116, instance <staking_contract::Store>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'$1_staking_contract_Store'($1_from_bcs_deserialize'$1_staking_contract_Store'(b1), $1_from_bcs_deserialize'$1_staking_contract_Store'(b2)) ==> $IsEqual'vec'u8''(b1, b2))));

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

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:18:9+124, instance <vector<u8>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'bool'($1_from_bcs_deserializable'vec'u8''(b1), $1_from_bcs_deserializable'vec'u8''(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:18:9+124, instance <vector<address>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'bool'($1_from_bcs_deserializable'vec'address''(b1), $1_from_bcs_deserializable'vec'address''(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:18:9+124, instance <vector<aggregator::Aggregator>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'bool'($1_from_bcs_deserializable'vec'$1_aggregator_Aggregator''(b1), $1_from_bcs_deserializable'vec'$1_aggregator_Aggregator''(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:18:9+124, instance <vector<optional_aggregator::Integer>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'bool'($1_from_bcs_deserializable'vec'$1_optional_aggregator_Integer''(b1), $1_from_bcs_deserializable'vec'$1_optional_aggregator_Integer''(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:18:9+124, instance <vector<optional_aggregator::OptionalAggregator>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'bool'($1_from_bcs_deserializable'vec'$1_optional_aggregator_OptionalAggregator''(b1), $1_from_bcs_deserializable'vec'$1_optional_aggregator_OptionalAggregator''(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:18:9+124, instance <vector<stake::IndividualValidatorPerformance>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'bool'($1_from_bcs_deserializable'vec'$1_stake_IndividualValidatorPerformance''(b1), $1_from_bcs_deserializable'vec'$1_stake_IndividualValidatorPerformance''(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:18:9+124, instance <vector<stake::ValidatorInfo>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'bool'($1_from_bcs_deserializable'vec'$1_stake_ValidatorInfo''(b1), $1_from_bcs_deserializable'vec'$1_stake_ValidatorInfo''(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:18:9+124, instance <vector<#0>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'bool'($1_from_bcs_deserializable'vec'#0''(b1), $1_from_bcs_deserializable'vec'#0''(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:18:9+124, instance <option::Option<aggregator::Aggregator>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'bool'($1_from_bcs_deserializable'$1_option_Option'$1_aggregator_Aggregator''(b1), $1_from_bcs_deserializable'$1_option_Option'$1_aggregator_Aggregator''(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:18:9+124, instance <option::Option<optional_aggregator::Integer>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'bool'($1_from_bcs_deserializable'$1_option_Option'$1_optional_aggregator_Integer''(b1), $1_from_bcs_deserializable'$1_option_Option'$1_optional_aggregator_Integer''(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:18:9+124, instance <option::Option<optional_aggregator::OptionalAggregator>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'bool'($1_from_bcs_deserializable'$1_option_Option'$1_optional_aggregator_OptionalAggregator''(b1), $1_from_bcs_deserializable'$1_option_Option'$1_optional_aggregator_OptionalAggregator''(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:18:9+124, instance <string::String>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'bool'($1_from_bcs_deserializable'$1_string_String'(b1), $1_from_bcs_deserializable'$1_string_String'(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:18:9+124, instance <type_info::TypeInfo>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'bool'($1_from_bcs_deserializable'$1_type_info_TypeInfo'(b1), $1_from_bcs_deserializable'$1_type_info_TypeInfo'(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:18:9+124, instance <guid::GUID>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'bool'($1_from_bcs_deserializable'$1_guid_GUID'(b1), $1_from_bcs_deserializable'$1_guid_GUID'(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:18:9+124, instance <guid::ID>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'bool'($1_from_bcs_deserializable'$1_guid_ID'(b1), $1_from_bcs_deserializable'$1_guid_ID'(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:18:9+124, instance <event::EventHandle<stake::AddStakeEvent>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'bool'($1_from_bcs_deserializable'$1_event_EventHandle'$1_stake_AddStakeEvent''(b1), $1_from_bcs_deserializable'$1_event_EventHandle'$1_stake_AddStakeEvent''(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:18:9+124, instance <event::EventHandle<stake::DistributeRewardsEvent>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'bool'($1_from_bcs_deserializable'$1_event_EventHandle'$1_stake_DistributeRewardsEvent''(b1), $1_from_bcs_deserializable'$1_event_EventHandle'$1_stake_DistributeRewardsEvent''(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:18:9+124, instance <event::EventHandle<stake::IncreaseLockupEvent>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'bool'($1_from_bcs_deserializable'$1_event_EventHandle'$1_stake_IncreaseLockupEvent''(b1), $1_from_bcs_deserializable'$1_event_EventHandle'$1_stake_IncreaseLockupEvent''(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:18:9+124, instance <event::EventHandle<stake::JoinValidatorSetEvent>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'bool'($1_from_bcs_deserializable'$1_event_EventHandle'$1_stake_JoinValidatorSetEvent''(b1), $1_from_bcs_deserializable'$1_event_EventHandle'$1_stake_JoinValidatorSetEvent''(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:18:9+124, instance <event::EventHandle<stake::LeaveValidatorSetEvent>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'bool'($1_from_bcs_deserializable'$1_event_EventHandle'$1_stake_LeaveValidatorSetEvent''(b1), $1_from_bcs_deserializable'$1_event_EventHandle'$1_stake_LeaveValidatorSetEvent''(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:18:9+124, instance <event::EventHandle<stake::ReactivateStakeEvent>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'bool'($1_from_bcs_deserializable'$1_event_EventHandle'$1_stake_ReactivateStakeEvent''(b1), $1_from_bcs_deserializable'$1_event_EventHandle'$1_stake_ReactivateStakeEvent''(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:18:9+124, instance <event::EventHandle<stake::RegisterValidatorCandidateEvent>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'bool'($1_from_bcs_deserializable'$1_event_EventHandle'$1_stake_RegisterValidatorCandidateEvent''(b1), $1_from_bcs_deserializable'$1_event_EventHandle'$1_stake_RegisterValidatorCandidateEvent''(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:18:9+124, instance <event::EventHandle<stake::RotateConsensusKeyEvent>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'bool'($1_from_bcs_deserializable'$1_event_EventHandle'$1_stake_RotateConsensusKeyEvent''(b1), $1_from_bcs_deserializable'$1_event_EventHandle'$1_stake_RotateConsensusKeyEvent''(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:18:9+124, instance <event::EventHandle<stake::SetOperatorEvent>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'bool'($1_from_bcs_deserializable'$1_event_EventHandle'$1_stake_SetOperatorEvent''(b1), $1_from_bcs_deserializable'$1_event_EventHandle'$1_stake_SetOperatorEvent''(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:18:9+124, instance <event::EventHandle<stake::UnlockStakeEvent>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'bool'($1_from_bcs_deserializable'$1_event_EventHandle'$1_stake_UnlockStakeEvent''(b1), $1_from_bcs_deserializable'$1_event_EventHandle'$1_stake_UnlockStakeEvent''(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:18:9+124, instance <event::EventHandle<stake::UpdateNetworkAndFullnodeAddressesEvent>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'bool'($1_from_bcs_deserializable'$1_event_EventHandle'$1_stake_UpdateNetworkAndFullnodeAddressesEvent''(b1), $1_from_bcs_deserializable'$1_event_EventHandle'$1_stake_UpdateNetworkAndFullnodeAddressesEvent''(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:18:9+124, instance <event::EventHandle<stake::WithdrawStakeEvent>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'bool'($1_from_bcs_deserializable'$1_event_EventHandle'$1_stake_WithdrawStakeEvent''(b1), $1_from_bcs_deserializable'$1_event_EventHandle'$1_stake_WithdrawStakeEvent''(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:18:9+124, instance <event::EventHandle<staking_contract::AddStakeEvent>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'bool'($1_from_bcs_deserializable'$1_event_EventHandle'$1_staking_contract_AddStakeEvent''(b1), $1_from_bcs_deserializable'$1_event_EventHandle'$1_staking_contract_AddStakeEvent''(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:18:9+124, instance <event::EventHandle<staking_contract::UnlockStakeEvent>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'bool'($1_from_bcs_deserializable'$1_event_EventHandle'$1_staking_contract_UnlockStakeEvent''(b1), $1_from_bcs_deserializable'$1_event_EventHandle'$1_staking_contract_UnlockStakeEvent''(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:18:9+124, instance <event::EventHandle<staking_contract::AddDistributionEvent>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'bool'($1_from_bcs_deserializable'$1_event_EventHandle'$1_staking_contract_AddDistributionEvent''(b1), $1_from_bcs_deserializable'$1_event_EventHandle'$1_staking_contract_AddDistributionEvent''(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:18:9+124, instance <event::EventHandle<staking_contract::CreateStakingContractEvent>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'bool'($1_from_bcs_deserializable'$1_event_EventHandle'$1_staking_contract_CreateStakingContractEvent''(b1), $1_from_bcs_deserializable'$1_event_EventHandle'$1_staking_contract_CreateStakingContractEvent''(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:18:9+124, instance <event::EventHandle<staking_contract::DistributeEvent>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'bool'($1_from_bcs_deserializable'$1_event_EventHandle'$1_staking_contract_DistributeEvent''(b1), $1_from_bcs_deserializable'$1_event_EventHandle'$1_staking_contract_DistributeEvent''(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:18:9+124, instance <event::EventHandle<staking_contract::RequestCommissionEvent>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'bool'($1_from_bcs_deserializable'$1_event_EventHandle'$1_staking_contract_RequestCommissionEvent''(b1), $1_from_bcs_deserializable'$1_event_EventHandle'$1_staking_contract_RequestCommissionEvent''(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:18:9+124, instance <event::EventHandle<staking_contract::ResetLockupEvent>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'bool'($1_from_bcs_deserializable'$1_event_EventHandle'$1_staking_contract_ResetLockupEvent''(b1), $1_from_bcs_deserializable'$1_event_EventHandle'$1_staking_contract_ResetLockupEvent''(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:18:9+124, instance <event::EventHandle<staking_contract::SwitchOperatorEvent>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'bool'($1_from_bcs_deserializable'$1_event_EventHandle'$1_staking_contract_SwitchOperatorEvent''(b1), $1_from_bcs_deserializable'$1_event_EventHandle'$1_staking_contract_SwitchOperatorEvent''(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:18:9+124, instance <event::EventHandle<staking_contract::UpdateVoterEvent>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'bool'($1_from_bcs_deserializable'$1_event_EventHandle'$1_staking_contract_UpdateVoterEvent''(b1), $1_from_bcs_deserializable'$1_event_EventHandle'$1_staking_contract_UpdateVoterEvent''(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:18:9+124, instance <account::SignerCapability>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'bool'($1_from_bcs_deserializable'$1_account_SignerCapability'(b1), $1_from_bcs_deserializable'$1_account_SignerCapability'(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:18:9+124, instance <aggregator::Aggregator>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'bool'($1_from_bcs_deserializable'$1_aggregator_Aggregator'(b1), $1_from_bcs_deserializable'$1_aggregator_Aggregator'(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:18:9+124, instance <optional_aggregator::Integer>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'bool'($1_from_bcs_deserializable'$1_optional_aggregator_Integer'(b1), $1_from_bcs_deserializable'$1_optional_aggregator_Integer'(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:18:9+124, instance <optional_aggregator::OptionalAggregator>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'bool'($1_from_bcs_deserializable'$1_optional_aggregator_OptionalAggregator'(b1), $1_from_bcs_deserializable'$1_optional_aggregator_OptionalAggregator'(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:18:9+124, instance <coin::Coin<aptos_coin::AptosCoin>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'bool'($1_from_bcs_deserializable'$1_coin_Coin'$1_aptos_coin_AptosCoin''(b1), $1_from_bcs_deserializable'$1_coin_Coin'$1_aptos_coin_AptosCoin''(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:18:9+124, instance <coin::CoinInfo<aptos_coin::AptosCoin>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'bool'($1_from_bcs_deserializable'$1_coin_CoinInfo'$1_aptos_coin_AptosCoin''(b1), $1_from_bcs_deserializable'$1_coin_CoinInfo'$1_aptos_coin_AptosCoin''(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:18:9+124, instance <coin::Ghost$supply<aptos_coin::AptosCoin>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'bool'($1_from_bcs_deserializable'$1_coin_Ghost$supply'$1_aptos_coin_AptosCoin''(b1), $1_from_bcs_deserializable'$1_coin_Ghost$supply'$1_aptos_coin_AptosCoin''(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:18:9+124, instance <coin::Ghost$aggregate_supply<aptos_coin::AptosCoin>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'bool'($1_from_bcs_deserializable'$1_coin_Ghost$aggregate_supply'$1_aptos_coin_AptosCoin''(b1), $1_from_bcs_deserializable'$1_coin_Ghost$aggregate_supply'$1_aptos_coin_AptosCoin''(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:18:9+124, instance <aptos_coin::AptosCoin>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'bool'($1_from_bcs_deserializable'$1_aptos_coin_AptosCoin'(b1), $1_from_bcs_deserializable'$1_aptos_coin_AptosCoin'(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:18:9+124, instance <simple_map::SimpleMap<address, u64>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'bool'($1_from_bcs_deserializable'$1_simple_map_SimpleMap'address_u64''(b1), $1_from_bcs_deserializable'$1_simple_map_SimpleMap'address_u64''(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:18:9+124, instance <simple_map::SimpleMap<address, staking_contract::StakingContract>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'bool'($1_from_bcs_deserializable'$1_simple_map_SimpleMap'address_$1_staking_contract_StakingContract''(b1), $1_from_bcs_deserializable'$1_simple_map_SimpleMap'address_$1_staking_contract_StakingContract''(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:18:9+124, instance <stake::OwnerCapability>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'bool'($1_from_bcs_deserializable'$1_stake_OwnerCapability'(b1), $1_from_bcs_deserializable'$1_stake_OwnerCapability'(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:18:9+124, instance <stake::StakePool>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'bool'($1_from_bcs_deserializable'$1_stake_StakePool'(b1), $1_from_bcs_deserializable'$1_stake_StakePool'(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:18:9+124, instance <stake::ValidatorConfig>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'bool'($1_from_bcs_deserializable'$1_stake_ValidatorConfig'(b1), $1_from_bcs_deserializable'$1_stake_ValidatorConfig'(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:18:9+124, instance <stake::ValidatorPerformance>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'bool'($1_from_bcs_deserializable'$1_stake_ValidatorPerformance'(b1), $1_from_bcs_deserializable'$1_stake_ValidatorPerformance'(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:18:9+124, instance <stake::ValidatorSet>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'bool'($1_from_bcs_deserializable'$1_stake_ValidatorSet'(b1), $1_from_bcs_deserializable'$1_stake_ValidatorSet'(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:18:9+124, instance <pool_u64::Pool>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'bool'($1_from_bcs_deserializable'$1_pool_u64_Pool'(b1), $1_from_bcs_deserializable'$1_pool_u64_Pool'(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:18:9+124, instance <staking_contract::StakingContract>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'bool'($1_from_bcs_deserializable'$1_staking_contract_StakingContract'(b1), $1_from_bcs_deserializable'$1_staking_contract_StakingContract'(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:18:9+124, instance <staking_contract::Store>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'bool'($1_from_bcs_deserializable'$1_staking_contract_Store'(b1), $1_from_bcs_deserializable'$1_staking_contract_Store'(b2)))));

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

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:21:9+118, instance <vector<u8>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'vec'u8''($1_from_bcs_deserialize'vec'u8''(b1), $1_from_bcs_deserialize'vec'u8''(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:21:9+118, instance <vector<address>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'vec'address''($1_from_bcs_deserialize'vec'address''(b1), $1_from_bcs_deserialize'vec'address''(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:21:9+118, instance <vector<aggregator::Aggregator>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'vec'$1_aggregator_Aggregator''($1_from_bcs_deserialize'vec'$1_aggregator_Aggregator''(b1), $1_from_bcs_deserialize'vec'$1_aggregator_Aggregator''(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:21:9+118, instance <vector<optional_aggregator::Integer>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'vec'$1_optional_aggregator_Integer''($1_from_bcs_deserialize'vec'$1_optional_aggregator_Integer''(b1), $1_from_bcs_deserialize'vec'$1_optional_aggregator_Integer''(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:21:9+118, instance <vector<optional_aggregator::OptionalAggregator>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'vec'$1_optional_aggregator_OptionalAggregator''($1_from_bcs_deserialize'vec'$1_optional_aggregator_OptionalAggregator''(b1), $1_from_bcs_deserialize'vec'$1_optional_aggregator_OptionalAggregator''(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:21:9+118, instance <vector<stake::IndividualValidatorPerformance>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'vec'$1_stake_IndividualValidatorPerformance''($1_from_bcs_deserialize'vec'$1_stake_IndividualValidatorPerformance''(b1), $1_from_bcs_deserialize'vec'$1_stake_IndividualValidatorPerformance''(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:21:9+118, instance <vector<stake::ValidatorInfo>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'vec'$1_stake_ValidatorInfo''($1_from_bcs_deserialize'vec'$1_stake_ValidatorInfo''(b1), $1_from_bcs_deserialize'vec'$1_stake_ValidatorInfo''(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:21:9+118, instance <vector<#0>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'vec'#0''($1_from_bcs_deserialize'vec'#0''(b1), $1_from_bcs_deserialize'vec'#0''(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:21:9+118, instance <option::Option<aggregator::Aggregator>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'$1_option_Option'$1_aggregator_Aggregator''($1_from_bcs_deserialize'$1_option_Option'$1_aggregator_Aggregator''(b1), $1_from_bcs_deserialize'$1_option_Option'$1_aggregator_Aggregator''(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:21:9+118, instance <option::Option<optional_aggregator::Integer>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'$1_option_Option'$1_optional_aggregator_Integer''($1_from_bcs_deserialize'$1_option_Option'$1_optional_aggregator_Integer''(b1), $1_from_bcs_deserialize'$1_option_Option'$1_optional_aggregator_Integer''(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:21:9+118, instance <option::Option<optional_aggregator::OptionalAggregator>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'$1_option_Option'$1_optional_aggregator_OptionalAggregator''($1_from_bcs_deserialize'$1_option_Option'$1_optional_aggregator_OptionalAggregator''(b1), $1_from_bcs_deserialize'$1_option_Option'$1_optional_aggregator_OptionalAggregator''(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:21:9+118, instance <string::String>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'$1_string_String'($1_from_bcs_deserialize'$1_string_String'(b1), $1_from_bcs_deserialize'$1_string_String'(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:21:9+118, instance <type_info::TypeInfo>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'$1_type_info_TypeInfo'($1_from_bcs_deserialize'$1_type_info_TypeInfo'(b1), $1_from_bcs_deserialize'$1_type_info_TypeInfo'(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:21:9+118, instance <guid::GUID>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'$1_guid_GUID'($1_from_bcs_deserialize'$1_guid_GUID'(b1), $1_from_bcs_deserialize'$1_guid_GUID'(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:21:9+118, instance <guid::ID>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'$1_guid_ID'($1_from_bcs_deserialize'$1_guid_ID'(b1), $1_from_bcs_deserialize'$1_guid_ID'(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:21:9+118, instance <event::EventHandle<stake::AddStakeEvent>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'$1_event_EventHandle'$1_stake_AddStakeEvent''($1_from_bcs_deserialize'$1_event_EventHandle'$1_stake_AddStakeEvent''(b1), $1_from_bcs_deserialize'$1_event_EventHandle'$1_stake_AddStakeEvent''(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:21:9+118, instance <event::EventHandle<stake::DistributeRewardsEvent>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'$1_event_EventHandle'$1_stake_DistributeRewardsEvent''($1_from_bcs_deserialize'$1_event_EventHandle'$1_stake_DistributeRewardsEvent''(b1), $1_from_bcs_deserialize'$1_event_EventHandle'$1_stake_DistributeRewardsEvent''(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:21:9+118, instance <event::EventHandle<stake::IncreaseLockupEvent>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'$1_event_EventHandle'$1_stake_IncreaseLockupEvent''($1_from_bcs_deserialize'$1_event_EventHandle'$1_stake_IncreaseLockupEvent''(b1), $1_from_bcs_deserialize'$1_event_EventHandle'$1_stake_IncreaseLockupEvent''(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:21:9+118, instance <event::EventHandle<stake::JoinValidatorSetEvent>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'$1_event_EventHandle'$1_stake_JoinValidatorSetEvent''($1_from_bcs_deserialize'$1_event_EventHandle'$1_stake_JoinValidatorSetEvent''(b1), $1_from_bcs_deserialize'$1_event_EventHandle'$1_stake_JoinValidatorSetEvent''(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:21:9+118, instance <event::EventHandle<stake::LeaveValidatorSetEvent>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'$1_event_EventHandle'$1_stake_LeaveValidatorSetEvent''($1_from_bcs_deserialize'$1_event_EventHandle'$1_stake_LeaveValidatorSetEvent''(b1), $1_from_bcs_deserialize'$1_event_EventHandle'$1_stake_LeaveValidatorSetEvent''(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:21:9+118, instance <event::EventHandle<stake::ReactivateStakeEvent>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'$1_event_EventHandle'$1_stake_ReactivateStakeEvent''($1_from_bcs_deserialize'$1_event_EventHandle'$1_stake_ReactivateStakeEvent''(b1), $1_from_bcs_deserialize'$1_event_EventHandle'$1_stake_ReactivateStakeEvent''(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:21:9+118, instance <event::EventHandle<stake::RegisterValidatorCandidateEvent>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'$1_event_EventHandle'$1_stake_RegisterValidatorCandidateEvent''($1_from_bcs_deserialize'$1_event_EventHandle'$1_stake_RegisterValidatorCandidateEvent''(b1), $1_from_bcs_deserialize'$1_event_EventHandle'$1_stake_RegisterValidatorCandidateEvent''(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:21:9+118, instance <event::EventHandle<stake::RotateConsensusKeyEvent>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'$1_event_EventHandle'$1_stake_RotateConsensusKeyEvent''($1_from_bcs_deserialize'$1_event_EventHandle'$1_stake_RotateConsensusKeyEvent''(b1), $1_from_bcs_deserialize'$1_event_EventHandle'$1_stake_RotateConsensusKeyEvent''(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:21:9+118, instance <event::EventHandle<stake::SetOperatorEvent>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'$1_event_EventHandle'$1_stake_SetOperatorEvent''($1_from_bcs_deserialize'$1_event_EventHandle'$1_stake_SetOperatorEvent''(b1), $1_from_bcs_deserialize'$1_event_EventHandle'$1_stake_SetOperatorEvent''(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:21:9+118, instance <event::EventHandle<stake::UnlockStakeEvent>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'$1_event_EventHandle'$1_stake_UnlockStakeEvent''($1_from_bcs_deserialize'$1_event_EventHandle'$1_stake_UnlockStakeEvent''(b1), $1_from_bcs_deserialize'$1_event_EventHandle'$1_stake_UnlockStakeEvent''(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:21:9+118, instance <event::EventHandle<stake::UpdateNetworkAndFullnodeAddressesEvent>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'$1_event_EventHandle'$1_stake_UpdateNetworkAndFullnodeAddressesEvent''($1_from_bcs_deserialize'$1_event_EventHandle'$1_stake_UpdateNetworkAndFullnodeAddressesEvent''(b1), $1_from_bcs_deserialize'$1_event_EventHandle'$1_stake_UpdateNetworkAndFullnodeAddressesEvent''(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:21:9+118, instance <event::EventHandle<stake::WithdrawStakeEvent>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'$1_event_EventHandle'$1_stake_WithdrawStakeEvent''($1_from_bcs_deserialize'$1_event_EventHandle'$1_stake_WithdrawStakeEvent''(b1), $1_from_bcs_deserialize'$1_event_EventHandle'$1_stake_WithdrawStakeEvent''(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:21:9+118, instance <event::EventHandle<staking_contract::AddStakeEvent>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'$1_event_EventHandle'$1_staking_contract_AddStakeEvent''($1_from_bcs_deserialize'$1_event_EventHandle'$1_staking_contract_AddStakeEvent''(b1), $1_from_bcs_deserialize'$1_event_EventHandle'$1_staking_contract_AddStakeEvent''(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:21:9+118, instance <event::EventHandle<staking_contract::UnlockStakeEvent>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'$1_event_EventHandle'$1_staking_contract_UnlockStakeEvent''($1_from_bcs_deserialize'$1_event_EventHandle'$1_staking_contract_UnlockStakeEvent''(b1), $1_from_bcs_deserialize'$1_event_EventHandle'$1_staking_contract_UnlockStakeEvent''(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:21:9+118, instance <event::EventHandle<staking_contract::AddDistributionEvent>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'$1_event_EventHandle'$1_staking_contract_AddDistributionEvent''($1_from_bcs_deserialize'$1_event_EventHandle'$1_staking_contract_AddDistributionEvent''(b1), $1_from_bcs_deserialize'$1_event_EventHandle'$1_staking_contract_AddDistributionEvent''(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:21:9+118, instance <event::EventHandle<staking_contract::CreateStakingContractEvent>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'$1_event_EventHandle'$1_staking_contract_CreateStakingContractEvent''($1_from_bcs_deserialize'$1_event_EventHandle'$1_staking_contract_CreateStakingContractEvent''(b1), $1_from_bcs_deserialize'$1_event_EventHandle'$1_staking_contract_CreateStakingContractEvent''(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:21:9+118, instance <event::EventHandle<staking_contract::DistributeEvent>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'$1_event_EventHandle'$1_staking_contract_DistributeEvent''($1_from_bcs_deserialize'$1_event_EventHandle'$1_staking_contract_DistributeEvent''(b1), $1_from_bcs_deserialize'$1_event_EventHandle'$1_staking_contract_DistributeEvent''(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:21:9+118, instance <event::EventHandle<staking_contract::RequestCommissionEvent>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'$1_event_EventHandle'$1_staking_contract_RequestCommissionEvent''($1_from_bcs_deserialize'$1_event_EventHandle'$1_staking_contract_RequestCommissionEvent''(b1), $1_from_bcs_deserialize'$1_event_EventHandle'$1_staking_contract_RequestCommissionEvent''(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:21:9+118, instance <event::EventHandle<staking_contract::ResetLockupEvent>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'$1_event_EventHandle'$1_staking_contract_ResetLockupEvent''($1_from_bcs_deserialize'$1_event_EventHandle'$1_staking_contract_ResetLockupEvent''(b1), $1_from_bcs_deserialize'$1_event_EventHandle'$1_staking_contract_ResetLockupEvent''(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:21:9+118, instance <event::EventHandle<staking_contract::SwitchOperatorEvent>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'$1_event_EventHandle'$1_staking_contract_SwitchOperatorEvent''($1_from_bcs_deserialize'$1_event_EventHandle'$1_staking_contract_SwitchOperatorEvent''(b1), $1_from_bcs_deserialize'$1_event_EventHandle'$1_staking_contract_SwitchOperatorEvent''(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:21:9+118, instance <event::EventHandle<staking_contract::UpdateVoterEvent>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'$1_event_EventHandle'$1_staking_contract_UpdateVoterEvent''($1_from_bcs_deserialize'$1_event_EventHandle'$1_staking_contract_UpdateVoterEvent''(b1), $1_from_bcs_deserialize'$1_event_EventHandle'$1_staking_contract_UpdateVoterEvent''(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:21:9+118, instance <account::SignerCapability>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'$1_account_SignerCapability'($1_from_bcs_deserialize'$1_account_SignerCapability'(b1), $1_from_bcs_deserialize'$1_account_SignerCapability'(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:21:9+118, instance <aggregator::Aggregator>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'$1_aggregator_Aggregator'($1_from_bcs_deserialize'$1_aggregator_Aggregator'(b1), $1_from_bcs_deserialize'$1_aggregator_Aggregator'(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:21:9+118, instance <optional_aggregator::Integer>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'$1_optional_aggregator_Integer'($1_from_bcs_deserialize'$1_optional_aggregator_Integer'(b1), $1_from_bcs_deserialize'$1_optional_aggregator_Integer'(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:21:9+118, instance <optional_aggregator::OptionalAggregator>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'$1_optional_aggregator_OptionalAggregator'($1_from_bcs_deserialize'$1_optional_aggregator_OptionalAggregator'(b1), $1_from_bcs_deserialize'$1_optional_aggregator_OptionalAggregator'(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:21:9+118, instance <coin::Coin<aptos_coin::AptosCoin>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'$1_coin_Coin'$1_aptos_coin_AptosCoin''($1_from_bcs_deserialize'$1_coin_Coin'$1_aptos_coin_AptosCoin''(b1), $1_from_bcs_deserialize'$1_coin_Coin'$1_aptos_coin_AptosCoin''(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:21:9+118, instance <coin::CoinInfo<aptos_coin::AptosCoin>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'$1_coin_CoinInfo'$1_aptos_coin_AptosCoin''($1_from_bcs_deserialize'$1_coin_CoinInfo'$1_aptos_coin_AptosCoin''(b1), $1_from_bcs_deserialize'$1_coin_CoinInfo'$1_aptos_coin_AptosCoin''(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:21:9+118, instance <coin::Ghost$supply<aptos_coin::AptosCoin>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'$1_coin_Ghost$supply'$1_aptos_coin_AptosCoin''($1_from_bcs_deserialize'$1_coin_Ghost$supply'$1_aptos_coin_AptosCoin''(b1), $1_from_bcs_deserialize'$1_coin_Ghost$supply'$1_aptos_coin_AptosCoin''(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:21:9+118, instance <coin::Ghost$aggregate_supply<aptos_coin::AptosCoin>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'$1_coin_Ghost$aggregate_supply'$1_aptos_coin_AptosCoin''($1_from_bcs_deserialize'$1_coin_Ghost$aggregate_supply'$1_aptos_coin_AptosCoin''(b1), $1_from_bcs_deserialize'$1_coin_Ghost$aggregate_supply'$1_aptos_coin_AptosCoin''(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:21:9+118, instance <aptos_coin::AptosCoin>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'$1_aptos_coin_AptosCoin'($1_from_bcs_deserialize'$1_aptos_coin_AptosCoin'(b1), $1_from_bcs_deserialize'$1_aptos_coin_AptosCoin'(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:21:9+118, instance <simple_map::SimpleMap<address, u64>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'$1_simple_map_SimpleMap'address_u64''($1_from_bcs_deserialize'$1_simple_map_SimpleMap'address_u64''(b1), $1_from_bcs_deserialize'$1_simple_map_SimpleMap'address_u64''(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:21:9+118, instance <simple_map::SimpleMap<address, staking_contract::StakingContract>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'$1_simple_map_SimpleMap'address_$1_staking_contract_StakingContract''($1_from_bcs_deserialize'$1_simple_map_SimpleMap'address_$1_staking_contract_StakingContract''(b1), $1_from_bcs_deserialize'$1_simple_map_SimpleMap'address_$1_staking_contract_StakingContract''(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:21:9+118, instance <stake::OwnerCapability>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'$1_stake_OwnerCapability'($1_from_bcs_deserialize'$1_stake_OwnerCapability'(b1), $1_from_bcs_deserialize'$1_stake_OwnerCapability'(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:21:9+118, instance <stake::StakePool>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'$1_stake_StakePool'($1_from_bcs_deserialize'$1_stake_StakePool'(b1), $1_from_bcs_deserialize'$1_stake_StakePool'(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:21:9+118, instance <stake::ValidatorConfig>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'$1_stake_ValidatorConfig'($1_from_bcs_deserialize'$1_stake_ValidatorConfig'(b1), $1_from_bcs_deserialize'$1_stake_ValidatorConfig'(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:21:9+118, instance <stake::ValidatorPerformance>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'$1_stake_ValidatorPerformance'($1_from_bcs_deserialize'$1_stake_ValidatorPerformance'(b1), $1_from_bcs_deserialize'$1_stake_ValidatorPerformance'(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:21:9+118, instance <stake::ValidatorSet>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'$1_stake_ValidatorSet'($1_from_bcs_deserialize'$1_stake_ValidatorSet'(b1), $1_from_bcs_deserialize'$1_stake_ValidatorSet'(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:21:9+118, instance <pool_u64::Pool>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'$1_pool_u64_Pool'($1_from_bcs_deserialize'$1_pool_u64_Pool'(b1), $1_from_bcs_deserialize'$1_pool_u64_Pool'(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:21:9+118, instance <staking_contract::StakingContract>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'$1_staking_contract_StakingContract'($1_from_bcs_deserialize'$1_staking_contract_StakingContract'(b1), $1_from_bcs_deserialize'$1_staking_contract_StakingContract'(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:21:9+118, instance <staking_contract::Store>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'$1_staking_contract_Store'($1_from_bcs_deserialize'$1_staking_contract_Store'(b1), $1_from_bcs_deserialize'$1_staking_contract_Store'(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:21:9+118, instance <#0>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'#0'($1_from_bcs_deserialize'#0'(b1), $1_from_bcs_deserialize'#0'(b2)))));

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/../move-stdlib/sources/vector.move:146:5+86
function {:inline} $1_vector_$is_empty'$1_aggregator_Aggregator'(v: Vec ($1_aggregator_Aggregator)): bool {
    $IsEqual'u64'($1_vector_$length'$1_aggregator_Aggregator'(v), 0)
}

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/../move-stdlib/sources/vector.move:146:5+86
function {:inline} $1_vector_$is_empty'$1_optional_aggregator_Integer'(v: Vec ($1_optional_aggregator_Integer)): bool {
    $IsEqual'u64'($1_vector_$length'$1_optional_aggregator_Integer'(v), 0)
}

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/../move-stdlib/sources/vector.move:608:9+110
function {:inline} $1_vector_spec_contains'address'(v: Vec (int), e: int): bool {
    (var $range_0 := v; (exists $i_1: int :: InRangeVec($range_0, $i_1) && (var x := ReadVec($range_0, $i_1);
    ($IsEqual'address'(x, e)))))
}

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/../move-stdlib/sources/option.move:102:5+145
function {:inline} $1_option_$borrow'$1_aggregator_Aggregator'(t: $1_option_Option'$1_aggregator_Aggregator'): $1_aggregator_Aggregator {
    $1_vector_$borrow'$1_aggregator_Aggregator'($vec#$1_option_Option'$1_aggregator_Aggregator'(t), 0)
}

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/../move-stdlib/sources/option.move:102:5+145
function {:inline} $1_option_$borrow'$1_optional_aggregator_Integer'(t: $1_option_Option'$1_optional_aggregator_Integer'): $1_optional_aggregator_Integer {
    $1_vector_$borrow'$1_optional_aggregator_Integer'($vec#$1_option_Option'$1_optional_aggregator_Integer'(t), 0)
}

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/../move-stdlib/sources/option.move:61:5+95
function {:inline} $1_option_$is_none'$1_aggregator_Aggregator'(t: $1_option_Option'$1_aggregator_Aggregator'): bool {
    $1_vector_$is_empty'$1_aggregator_Aggregator'($vec#$1_option_Option'$1_aggregator_Aggregator'(t))
}

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/../move-stdlib/sources/option.move:61:5+95
function {:inline} $1_option_$is_none'$1_optional_aggregator_Integer'(t: $1_option_Option'$1_optional_aggregator_Integer'): bool {
    $1_vector_$is_empty'$1_optional_aggregator_Integer'($vec#$1_option_Option'$1_optional_aggregator_Integer'(t))
}

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/../move-stdlib/sources/option.move:74:5+96
function {:inline} $1_option_$is_some'$1_aggregator_Aggregator'(t: $1_option_Option'$1_aggregator_Aggregator'): bool {
    !$1_vector_$is_empty'$1_aggregator_Aggregator'($vec#$1_option_Option'$1_aggregator_Aggregator'(t))
}

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/../move-stdlib/sources/option.move:74:5+96
function {:inline} $1_option_$is_some'$1_optional_aggregator_Integer'(t: $1_option_Option'$1_optional_aggregator_Integer'): bool {
    !$1_vector_$is_empty'$1_optional_aggregator_Integer'($vec#$1_option_Option'$1_optional_aggregator_Integer'(t))
}

// struct option::Option<aggregator::Aggregator> at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/../move-stdlib/sources/option.move:7:5+81
type {:datatype} $1_option_Option'$1_aggregator_Aggregator';
function {:constructor} $1_option_Option'$1_aggregator_Aggregator'($vec: Vec ($1_aggregator_Aggregator)): $1_option_Option'$1_aggregator_Aggregator';
function {:inline} $Update'$1_option_Option'$1_aggregator_Aggregator''_vec(s: $1_option_Option'$1_aggregator_Aggregator', x: Vec ($1_aggregator_Aggregator)): $1_option_Option'$1_aggregator_Aggregator' {
    $1_option_Option'$1_aggregator_Aggregator'(x)
}
function $IsValid'$1_option_Option'$1_aggregator_Aggregator''(s: $1_option_Option'$1_aggregator_Aggregator'): bool {
    $IsValid'vec'$1_aggregator_Aggregator''($vec#$1_option_Option'$1_aggregator_Aggregator'(s))
}
function {:inline} $IsEqual'$1_option_Option'$1_aggregator_Aggregator''(s1: $1_option_Option'$1_aggregator_Aggregator', s2: $1_option_Option'$1_aggregator_Aggregator'): bool {
    $IsEqual'vec'$1_aggregator_Aggregator''($vec#$1_option_Option'$1_aggregator_Aggregator'(s1), $vec#$1_option_Option'$1_aggregator_Aggregator'(s2))}

// struct option::Option<optional_aggregator::Integer> at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/../move-stdlib/sources/option.move:7:5+81
type {:datatype} $1_option_Option'$1_optional_aggregator_Integer';
function {:constructor} $1_option_Option'$1_optional_aggregator_Integer'($vec: Vec ($1_optional_aggregator_Integer)): $1_option_Option'$1_optional_aggregator_Integer';
function {:inline} $Update'$1_option_Option'$1_optional_aggregator_Integer''_vec(s: $1_option_Option'$1_optional_aggregator_Integer', x: Vec ($1_optional_aggregator_Integer)): $1_option_Option'$1_optional_aggregator_Integer' {
    $1_option_Option'$1_optional_aggregator_Integer'(x)
}
function $IsValid'$1_option_Option'$1_optional_aggregator_Integer''(s: $1_option_Option'$1_optional_aggregator_Integer'): bool {
    $IsValid'vec'$1_optional_aggregator_Integer''($vec#$1_option_Option'$1_optional_aggregator_Integer'(s))
}
function {:inline} $IsEqual'$1_option_Option'$1_optional_aggregator_Integer''(s1: $1_option_Option'$1_optional_aggregator_Integer', s2: $1_option_Option'$1_optional_aggregator_Integer'): bool {
    $IsEqual'vec'$1_optional_aggregator_Integer''($vec#$1_option_Option'$1_optional_aggregator_Integer'(s1), $vec#$1_option_Option'$1_optional_aggregator_Integer'(s2))}

// struct option::Option<optional_aggregator::OptionalAggregator> at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/../move-stdlib/sources/option.move:7:5+81
type {:datatype} $1_option_Option'$1_optional_aggregator_OptionalAggregator';
function {:constructor} $1_option_Option'$1_optional_aggregator_OptionalAggregator'($vec: Vec ($1_optional_aggregator_OptionalAggregator)): $1_option_Option'$1_optional_aggregator_OptionalAggregator';
function {:inline} $Update'$1_option_Option'$1_optional_aggregator_OptionalAggregator''_vec(s: $1_option_Option'$1_optional_aggregator_OptionalAggregator', x: Vec ($1_optional_aggregator_OptionalAggregator)): $1_option_Option'$1_optional_aggregator_OptionalAggregator' {
    $1_option_Option'$1_optional_aggregator_OptionalAggregator'(x)
}
function $IsValid'$1_option_Option'$1_optional_aggregator_OptionalAggregator''(s: $1_option_Option'$1_optional_aggregator_OptionalAggregator'): bool {
    $IsValid'vec'$1_optional_aggregator_OptionalAggregator''($vec#$1_option_Option'$1_optional_aggregator_OptionalAggregator'(s))
}
function {:inline} $IsEqual'$1_option_Option'$1_optional_aggregator_OptionalAggregator''(s1: $1_option_Option'$1_optional_aggregator_OptionalAggregator', s2: $1_option_Option'$1_optional_aggregator_OptionalAggregator'): bool {
    $IsEqual'vec'$1_optional_aggregator_OptionalAggregator''($vec#$1_option_Option'$1_optional_aggregator_OptionalAggregator'(s1), $vec#$1_option_Option'$1_optional_aggregator_OptionalAggregator'(s2))}

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

// fun error::not_found [baseline] at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/../move-stdlib/sources/error.move:81:3+61
procedure {:inline 1} $1_error_not_found(_$t0: int) returns ($ret0: int)
{
    // declare local variables
    var $t1: int;
    var $t2: int;
    var $t3: int;
    var $t0: int;
    var $temp_0'u64': int;
    $t0 := _$t0;

    // bytecode translation starts here
    // trace_local[r]($t0) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/../move-stdlib/sources/error.move:81:3+1
    assume {:print "$at(10,3461,3462)"} true;
    assume {:print "$track_local(4,6,0):", $t0} $t0 == $t0;

    // $t1 := 6 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/../move-stdlib/sources/error.move:81:49+9
    $t1 := 6;
    assume $IsValid'u64'($t1);

    // assume Identical($t2, Shl($t1, 16)) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/../move-stdlib/sources/error.move:69:5+29
    assume {:print "$at(10,2844,2873)"} true;
    assume ($t2 == $shlU64($t1, 16));

    // $t3 := opaque begin: error::canonical($t1, $t0) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/../move-stdlib/sources/error.move:81:39+23
    assume {:print "$at(10,3497,3520)"} true;

    // assume WellFormed($t3) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/../move-stdlib/sources/error.move:81:39+23
    assume $IsValid'u64'($t3);

    // assume Eq<u64>($t3, $t1) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/../move-stdlib/sources/error.move:81:39+23
    assume $IsEqual'u64'($t3, $t1);

    // $t3 := opaque end: error::canonical($t1, $t0) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/../move-stdlib/sources/error.move:81:39+23

    // trace_return[0]($t3) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/../move-stdlib/sources/error.move:81:39+23
    assume {:print "$track_return(4,6,0):", $t3} $t3 == $t3;

    // label L1 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/../move-stdlib/sources/error.move:81:63+1
L1:

    // return $t3 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/../move-stdlib/sources/error.move:81:63+1
    assume {:print "$at(10,3521,3522)"} true;
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
function  $1_from_bcs_deserialize'vec'$1_aggregator_Aggregator''(bytes: Vec (int)): Vec ($1_aggregator_Aggregator);
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserialize'vec'$1_aggregator_Aggregator''(bytes);
$IsValid'vec'$1_aggregator_Aggregator''($$res)));

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:7:9+41
function  $1_from_bcs_deserialize'vec'$1_optional_aggregator_Integer''(bytes: Vec (int)): Vec ($1_optional_aggregator_Integer);
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserialize'vec'$1_optional_aggregator_Integer''(bytes);
$IsValid'vec'$1_optional_aggregator_Integer''($$res)));

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:7:9+41
function  $1_from_bcs_deserialize'vec'$1_optional_aggregator_OptionalAggregator''(bytes: Vec (int)): Vec ($1_optional_aggregator_OptionalAggregator);
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserialize'vec'$1_optional_aggregator_OptionalAggregator''(bytes);
$IsValid'vec'$1_optional_aggregator_OptionalAggregator''($$res)));

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
function  $1_from_bcs_deserialize'vec'#0''(bytes: Vec (int)): Vec (#0);
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserialize'vec'#0''(bytes);
$IsValid'vec'#0''($$res)));

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:7:9+41
function  $1_from_bcs_deserialize'$1_option_Option'$1_aggregator_Aggregator''(bytes: Vec (int)): $1_option_Option'$1_aggregator_Aggregator';
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserialize'$1_option_Option'$1_aggregator_Aggregator''(bytes);
$IsValid'$1_option_Option'$1_aggregator_Aggregator''($$res)));

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:7:9+41
function  $1_from_bcs_deserialize'$1_option_Option'$1_optional_aggregator_Integer''(bytes: Vec (int)): $1_option_Option'$1_optional_aggregator_Integer';
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserialize'$1_option_Option'$1_optional_aggregator_Integer''(bytes);
$IsValid'$1_option_Option'$1_optional_aggregator_Integer''($$res)));

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:7:9+41
function  $1_from_bcs_deserialize'$1_option_Option'$1_optional_aggregator_OptionalAggregator''(bytes: Vec (int)): $1_option_Option'$1_optional_aggregator_OptionalAggregator';
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserialize'$1_option_Option'$1_optional_aggregator_OptionalAggregator''(bytes);
$IsValid'$1_option_Option'$1_optional_aggregator_OptionalAggregator''($$res)));

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
function  $1_from_bcs_deserialize'$1_event_EventHandle'$1_stake_AddStakeEvent''(bytes: Vec (int)): $1_event_EventHandle'$1_stake_AddStakeEvent';
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserialize'$1_event_EventHandle'$1_stake_AddStakeEvent''(bytes);
$IsValid'$1_event_EventHandle'$1_stake_AddStakeEvent''($$res)));

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:7:9+41
function  $1_from_bcs_deserialize'$1_event_EventHandle'$1_stake_DistributeRewardsEvent''(bytes: Vec (int)): $1_event_EventHandle'$1_stake_DistributeRewardsEvent';
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserialize'$1_event_EventHandle'$1_stake_DistributeRewardsEvent''(bytes);
$IsValid'$1_event_EventHandle'$1_stake_DistributeRewardsEvent''($$res)));

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:7:9+41
function  $1_from_bcs_deserialize'$1_event_EventHandle'$1_stake_IncreaseLockupEvent''(bytes: Vec (int)): $1_event_EventHandle'$1_stake_IncreaseLockupEvent';
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserialize'$1_event_EventHandle'$1_stake_IncreaseLockupEvent''(bytes);
$IsValid'$1_event_EventHandle'$1_stake_IncreaseLockupEvent''($$res)));

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:7:9+41
function  $1_from_bcs_deserialize'$1_event_EventHandle'$1_stake_JoinValidatorSetEvent''(bytes: Vec (int)): $1_event_EventHandle'$1_stake_JoinValidatorSetEvent';
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserialize'$1_event_EventHandle'$1_stake_JoinValidatorSetEvent''(bytes);
$IsValid'$1_event_EventHandle'$1_stake_JoinValidatorSetEvent''($$res)));

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:7:9+41
function  $1_from_bcs_deserialize'$1_event_EventHandle'$1_stake_LeaveValidatorSetEvent''(bytes: Vec (int)): $1_event_EventHandle'$1_stake_LeaveValidatorSetEvent';
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserialize'$1_event_EventHandle'$1_stake_LeaveValidatorSetEvent''(bytes);
$IsValid'$1_event_EventHandle'$1_stake_LeaveValidatorSetEvent''($$res)));

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:7:9+41
function  $1_from_bcs_deserialize'$1_event_EventHandle'$1_stake_ReactivateStakeEvent''(bytes: Vec (int)): $1_event_EventHandle'$1_stake_ReactivateStakeEvent';
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserialize'$1_event_EventHandle'$1_stake_ReactivateStakeEvent''(bytes);
$IsValid'$1_event_EventHandle'$1_stake_ReactivateStakeEvent''($$res)));

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:7:9+41
function  $1_from_bcs_deserialize'$1_event_EventHandle'$1_stake_RegisterValidatorCandidateEvent''(bytes: Vec (int)): $1_event_EventHandle'$1_stake_RegisterValidatorCandidateEvent';
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserialize'$1_event_EventHandle'$1_stake_RegisterValidatorCandidateEvent''(bytes);
$IsValid'$1_event_EventHandle'$1_stake_RegisterValidatorCandidateEvent''($$res)));

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:7:9+41
function  $1_from_bcs_deserialize'$1_event_EventHandle'$1_stake_RotateConsensusKeyEvent''(bytes: Vec (int)): $1_event_EventHandle'$1_stake_RotateConsensusKeyEvent';
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserialize'$1_event_EventHandle'$1_stake_RotateConsensusKeyEvent''(bytes);
$IsValid'$1_event_EventHandle'$1_stake_RotateConsensusKeyEvent''($$res)));

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:7:9+41
function  $1_from_bcs_deserialize'$1_event_EventHandle'$1_stake_SetOperatorEvent''(bytes: Vec (int)): $1_event_EventHandle'$1_stake_SetOperatorEvent';
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserialize'$1_event_EventHandle'$1_stake_SetOperatorEvent''(bytes);
$IsValid'$1_event_EventHandle'$1_stake_SetOperatorEvent''($$res)));

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:7:9+41
function  $1_from_bcs_deserialize'$1_event_EventHandle'$1_stake_UnlockStakeEvent''(bytes: Vec (int)): $1_event_EventHandle'$1_stake_UnlockStakeEvent';
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserialize'$1_event_EventHandle'$1_stake_UnlockStakeEvent''(bytes);
$IsValid'$1_event_EventHandle'$1_stake_UnlockStakeEvent''($$res)));

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:7:9+41
function  $1_from_bcs_deserialize'$1_event_EventHandle'$1_stake_UpdateNetworkAndFullnodeAddressesEvent''(bytes: Vec (int)): $1_event_EventHandle'$1_stake_UpdateNetworkAndFullnodeAddressesEvent';
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserialize'$1_event_EventHandle'$1_stake_UpdateNetworkAndFullnodeAddressesEvent''(bytes);
$IsValid'$1_event_EventHandle'$1_stake_UpdateNetworkAndFullnodeAddressesEvent''($$res)));

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:7:9+41
function  $1_from_bcs_deserialize'$1_event_EventHandle'$1_stake_WithdrawStakeEvent''(bytes: Vec (int)): $1_event_EventHandle'$1_stake_WithdrawStakeEvent';
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserialize'$1_event_EventHandle'$1_stake_WithdrawStakeEvent''(bytes);
$IsValid'$1_event_EventHandle'$1_stake_WithdrawStakeEvent''($$res)));

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:7:9+41
function  $1_from_bcs_deserialize'$1_event_EventHandle'$1_staking_contract_AddStakeEvent''(bytes: Vec (int)): $1_event_EventHandle'$1_staking_contract_AddStakeEvent';
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserialize'$1_event_EventHandle'$1_staking_contract_AddStakeEvent''(bytes);
$IsValid'$1_event_EventHandle'$1_staking_contract_AddStakeEvent''($$res)));

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:7:9+41
function  $1_from_bcs_deserialize'$1_event_EventHandle'$1_staking_contract_UnlockStakeEvent''(bytes: Vec (int)): $1_event_EventHandle'$1_staking_contract_UnlockStakeEvent';
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserialize'$1_event_EventHandle'$1_staking_contract_UnlockStakeEvent''(bytes);
$IsValid'$1_event_EventHandle'$1_staking_contract_UnlockStakeEvent''($$res)));

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:7:9+41
function  $1_from_bcs_deserialize'$1_event_EventHandle'$1_staking_contract_AddDistributionEvent''(bytes: Vec (int)): $1_event_EventHandle'$1_staking_contract_AddDistributionEvent';
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserialize'$1_event_EventHandle'$1_staking_contract_AddDistributionEvent''(bytes);
$IsValid'$1_event_EventHandle'$1_staking_contract_AddDistributionEvent''($$res)));

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:7:9+41
function  $1_from_bcs_deserialize'$1_event_EventHandle'$1_staking_contract_CreateStakingContractEvent''(bytes: Vec (int)): $1_event_EventHandle'$1_staking_contract_CreateStakingContractEvent';
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserialize'$1_event_EventHandle'$1_staking_contract_CreateStakingContractEvent''(bytes);
$IsValid'$1_event_EventHandle'$1_staking_contract_CreateStakingContractEvent''($$res)));

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:7:9+41
function  $1_from_bcs_deserialize'$1_event_EventHandle'$1_staking_contract_DistributeEvent''(bytes: Vec (int)): $1_event_EventHandle'$1_staking_contract_DistributeEvent';
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserialize'$1_event_EventHandle'$1_staking_contract_DistributeEvent''(bytes);
$IsValid'$1_event_EventHandle'$1_staking_contract_DistributeEvent''($$res)));

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:7:9+41
function  $1_from_bcs_deserialize'$1_event_EventHandle'$1_staking_contract_RequestCommissionEvent''(bytes: Vec (int)): $1_event_EventHandle'$1_staking_contract_RequestCommissionEvent';
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserialize'$1_event_EventHandle'$1_staking_contract_RequestCommissionEvent''(bytes);
$IsValid'$1_event_EventHandle'$1_staking_contract_RequestCommissionEvent''($$res)));

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:7:9+41
function  $1_from_bcs_deserialize'$1_event_EventHandle'$1_staking_contract_ResetLockupEvent''(bytes: Vec (int)): $1_event_EventHandle'$1_staking_contract_ResetLockupEvent';
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserialize'$1_event_EventHandle'$1_staking_contract_ResetLockupEvent''(bytes);
$IsValid'$1_event_EventHandle'$1_staking_contract_ResetLockupEvent''($$res)));

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:7:9+41
function  $1_from_bcs_deserialize'$1_event_EventHandle'$1_staking_contract_SwitchOperatorEvent''(bytes: Vec (int)): $1_event_EventHandle'$1_staking_contract_SwitchOperatorEvent';
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserialize'$1_event_EventHandle'$1_staking_contract_SwitchOperatorEvent''(bytes);
$IsValid'$1_event_EventHandle'$1_staking_contract_SwitchOperatorEvent''($$res)));

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:7:9+41
function  $1_from_bcs_deserialize'$1_event_EventHandle'$1_staking_contract_UpdateVoterEvent''(bytes: Vec (int)): $1_event_EventHandle'$1_staking_contract_UpdateVoterEvent';
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserialize'$1_event_EventHandle'$1_staking_contract_UpdateVoterEvent''(bytes);
$IsValid'$1_event_EventHandle'$1_staking_contract_UpdateVoterEvent''($$res)));

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:7:9+41
function  $1_from_bcs_deserialize'$1_account_SignerCapability'(bytes: Vec (int)): $1_account_SignerCapability;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserialize'$1_account_SignerCapability'(bytes);
$IsValid'$1_account_SignerCapability'($$res)));

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:7:9+41
function  $1_from_bcs_deserialize'$1_aggregator_Aggregator'(bytes: Vec (int)): $1_aggregator_Aggregator;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserialize'$1_aggregator_Aggregator'(bytes);
$IsValid'$1_aggregator_Aggregator'($$res)));

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:7:9+41
function  $1_from_bcs_deserialize'$1_optional_aggregator_Integer'(bytes: Vec (int)): $1_optional_aggregator_Integer;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserialize'$1_optional_aggregator_Integer'(bytes);
$IsValid'$1_optional_aggregator_Integer'($$res)));

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:7:9+41
function  $1_from_bcs_deserialize'$1_optional_aggregator_OptionalAggregator'(bytes: Vec (int)): $1_optional_aggregator_OptionalAggregator;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserialize'$1_optional_aggregator_OptionalAggregator'(bytes);
$IsValid'$1_optional_aggregator_OptionalAggregator'($$res)));

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:7:9+41
function  $1_from_bcs_deserialize'$1_coin_Coin'$1_aptos_coin_AptosCoin''(bytes: Vec (int)): $1_coin_Coin'$1_aptos_coin_AptosCoin';
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserialize'$1_coin_Coin'$1_aptos_coin_AptosCoin''(bytes);
$IsValid'$1_coin_Coin'$1_aptos_coin_AptosCoin''($$res)));

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:7:9+41
function  $1_from_bcs_deserialize'$1_coin_CoinInfo'$1_aptos_coin_AptosCoin''(bytes: Vec (int)): $1_coin_CoinInfo'$1_aptos_coin_AptosCoin';
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserialize'$1_coin_CoinInfo'$1_aptos_coin_AptosCoin''(bytes);
$IsValid'$1_coin_CoinInfo'$1_aptos_coin_AptosCoin''($$res)));

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:7:9+41
function  $1_from_bcs_deserialize'$1_coin_Ghost$supply'$1_aptos_coin_AptosCoin''(bytes: Vec (int)): $1_coin_Ghost$supply'$1_aptos_coin_AptosCoin';
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserialize'$1_coin_Ghost$supply'$1_aptos_coin_AptosCoin''(bytes);
$IsValid'$1_coin_Ghost$supply'$1_aptos_coin_AptosCoin''($$res)));

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:7:9+41
function  $1_from_bcs_deserialize'$1_coin_Ghost$aggregate_supply'$1_aptos_coin_AptosCoin''(bytes: Vec (int)): $1_coin_Ghost$aggregate_supply'$1_aptos_coin_AptosCoin';
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserialize'$1_coin_Ghost$aggregate_supply'$1_aptos_coin_AptosCoin''(bytes);
$IsValid'$1_coin_Ghost$aggregate_supply'$1_aptos_coin_AptosCoin''($$res)));

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:7:9+41
function  $1_from_bcs_deserialize'$1_aptos_coin_AptosCoin'(bytes: Vec (int)): $1_aptos_coin_AptosCoin;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserialize'$1_aptos_coin_AptosCoin'(bytes);
$IsValid'$1_aptos_coin_AptosCoin'($$res)));

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:7:9+41
function  $1_from_bcs_deserialize'$1_simple_map_SimpleMap'address_u64''(bytes: Vec (int)): Table int (int);
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserialize'$1_simple_map_SimpleMap'address_u64''(bytes);
$IsValid'$1_simple_map_SimpleMap'address_u64''($$res)));

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:7:9+41
function  $1_from_bcs_deserialize'$1_simple_map_SimpleMap'address_$1_staking_contract_StakingContract''(bytes: Vec (int)): Table int ($1_staking_contract_StakingContract);
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserialize'$1_simple_map_SimpleMap'address_$1_staking_contract_StakingContract''(bytes);
$IsValid'$1_simple_map_SimpleMap'address_$1_staking_contract_StakingContract''($$res)));

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:7:9+41
function  $1_from_bcs_deserialize'$1_stake_OwnerCapability'(bytes: Vec (int)): $1_stake_OwnerCapability;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserialize'$1_stake_OwnerCapability'(bytes);
$IsValid'$1_stake_OwnerCapability'($$res)));

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:7:9+41
function  $1_from_bcs_deserialize'$1_stake_StakePool'(bytes: Vec (int)): $1_stake_StakePool;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserialize'$1_stake_StakePool'(bytes);
$IsValid'$1_stake_StakePool'($$res)));

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
function  $1_from_bcs_deserialize'$1_pool_u64_Pool'(bytes: Vec (int)): $1_pool_u64_Pool;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserialize'$1_pool_u64_Pool'(bytes);
$IsValid'$1_pool_u64_Pool'($$res)));

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:7:9+41
function  $1_from_bcs_deserialize'$1_staking_contract_StakingContract'(bytes: Vec (int)): $1_staking_contract_StakingContract;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserialize'$1_staking_contract_StakingContract'(bytes);
$IsValid'$1_staking_contract_StakingContract'($$res)));

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:7:9+41
function  $1_from_bcs_deserialize'$1_staking_contract_Store'(bytes: Vec (int)): $1_staking_contract_Store;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserialize'$1_staking_contract_Store'(bytes);
$IsValid'$1_staking_contract_Store'($$res)));

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
function  $1_from_bcs_deserializable'vec'$1_aggregator_Aggregator''(bytes: Vec (int)): bool;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserializable'vec'$1_aggregator_Aggregator''(bytes);
$IsValid'bool'($$res)));

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:11:9+47
function  $1_from_bcs_deserializable'vec'$1_optional_aggregator_Integer''(bytes: Vec (int)): bool;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserializable'vec'$1_optional_aggregator_Integer''(bytes);
$IsValid'bool'($$res)));

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:11:9+47
function  $1_from_bcs_deserializable'vec'$1_optional_aggregator_OptionalAggregator''(bytes: Vec (int)): bool;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserializable'vec'$1_optional_aggregator_OptionalAggregator''(bytes);
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
function  $1_from_bcs_deserializable'vec'#0''(bytes: Vec (int)): bool;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserializable'vec'#0''(bytes);
$IsValid'bool'($$res)));

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:11:9+47
function  $1_from_bcs_deserializable'$1_option_Option'$1_aggregator_Aggregator''(bytes: Vec (int)): bool;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserializable'$1_option_Option'$1_aggregator_Aggregator''(bytes);
$IsValid'bool'($$res)));

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:11:9+47
function  $1_from_bcs_deserializable'$1_option_Option'$1_optional_aggregator_Integer''(bytes: Vec (int)): bool;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserializable'$1_option_Option'$1_optional_aggregator_Integer''(bytes);
$IsValid'bool'($$res)));

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:11:9+47
function  $1_from_bcs_deserializable'$1_option_Option'$1_optional_aggregator_OptionalAggregator''(bytes: Vec (int)): bool;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserializable'$1_option_Option'$1_optional_aggregator_OptionalAggregator''(bytes);
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
function  $1_from_bcs_deserializable'$1_event_EventHandle'$1_stake_AddStakeEvent''(bytes: Vec (int)): bool;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserializable'$1_event_EventHandle'$1_stake_AddStakeEvent''(bytes);
$IsValid'bool'($$res)));

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:11:9+47
function  $1_from_bcs_deserializable'$1_event_EventHandle'$1_stake_DistributeRewardsEvent''(bytes: Vec (int)): bool;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserializable'$1_event_EventHandle'$1_stake_DistributeRewardsEvent''(bytes);
$IsValid'bool'($$res)));

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:11:9+47
function  $1_from_bcs_deserializable'$1_event_EventHandle'$1_stake_IncreaseLockupEvent''(bytes: Vec (int)): bool;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserializable'$1_event_EventHandle'$1_stake_IncreaseLockupEvent''(bytes);
$IsValid'bool'($$res)));

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:11:9+47
function  $1_from_bcs_deserializable'$1_event_EventHandle'$1_stake_JoinValidatorSetEvent''(bytes: Vec (int)): bool;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserializable'$1_event_EventHandle'$1_stake_JoinValidatorSetEvent''(bytes);
$IsValid'bool'($$res)));

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:11:9+47
function  $1_from_bcs_deserializable'$1_event_EventHandle'$1_stake_LeaveValidatorSetEvent''(bytes: Vec (int)): bool;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserializable'$1_event_EventHandle'$1_stake_LeaveValidatorSetEvent''(bytes);
$IsValid'bool'($$res)));

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:11:9+47
function  $1_from_bcs_deserializable'$1_event_EventHandle'$1_stake_ReactivateStakeEvent''(bytes: Vec (int)): bool;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserializable'$1_event_EventHandle'$1_stake_ReactivateStakeEvent''(bytes);
$IsValid'bool'($$res)));

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:11:9+47
function  $1_from_bcs_deserializable'$1_event_EventHandle'$1_stake_RegisterValidatorCandidateEvent''(bytes: Vec (int)): bool;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserializable'$1_event_EventHandle'$1_stake_RegisterValidatorCandidateEvent''(bytes);
$IsValid'bool'($$res)));

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:11:9+47
function  $1_from_bcs_deserializable'$1_event_EventHandle'$1_stake_RotateConsensusKeyEvent''(bytes: Vec (int)): bool;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserializable'$1_event_EventHandle'$1_stake_RotateConsensusKeyEvent''(bytes);
$IsValid'bool'($$res)));

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:11:9+47
function  $1_from_bcs_deserializable'$1_event_EventHandle'$1_stake_SetOperatorEvent''(bytes: Vec (int)): bool;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserializable'$1_event_EventHandle'$1_stake_SetOperatorEvent''(bytes);
$IsValid'bool'($$res)));

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:11:9+47
function  $1_from_bcs_deserializable'$1_event_EventHandle'$1_stake_UnlockStakeEvent''(bytes: Vec (int)): bool;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserializable'$1_event_EventHandle'$1_stake_UnlockStakeEvent''(bytes);
$IsValid'bool'($$res)));

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:11:9+47
function  $1_from_bcs_deserializable'$1_event_EventHandle'$1_stake_UpdateNetworkAndFullnodeAddressesEvent''(bytes: Vec (int)): bool;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserializable'$1_event_EventHandle'$1_stake_UpdateNetworkAndFullnodeAddressesEvent''(bytes);
$IsValid'bool'($$res)));

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:11:9+47
function  $1_from_bcs_deserializable'$1_event_EventHandle'$1_stake_WithdrawStakeEvent''(bytes: Vec (int)): bool;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserializable'$1_event_EventHandle'$1_stake_WithdrawStakeEvent''(bytes);
$IsValid'bool'($$res)));

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:11:9+47
function  $1_from_bcs_deserializable'$1_event_EventHandle'$1_staking_contract_AddStakeEvent''(bytes: Vec (int)): bool;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserializable'$1_event_EventHandle'$1_staking_contract_AddStakeEvent''(bytes);
$IsValid'bool'($$res)));

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:11:9+47
function  $1_from_bcs_deserializable'$1_event_EventHandle'$1_staking_contract_UnlockStakeEvent''(bytes: Vec (int)): bool;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserializable'$1_event_EventHandle'$1_staking_contract_UnlockStakeEvent''(bytes);
$IsValid'bool'($$res)));

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:11:9+47
function  $1_from_bcs_deserializable'$1_event_EventHandle'$1_staking_contract_AddDistributionEvent''(bytes: Vec (int)): bool;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserializable'$1_event_EventHandle'$1_staking_contract_AddDistributionEvent''(bytes);
$IsValid'bool'($$res)));

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:11:9+47
function  $1_from_bcs_deserializable'$1_event_EventHandle'$1_staking_contract_CreateStakingContractEvent''(bytes: Vec (int)): bool;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserializable'$1_event_EventHandle'$1_staking_contract_CreateStakingContractEvent''(bytes);
$IsValid'bool'($$res)));

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:11:9+47
function  $1_from_bcs_deserializable'$1_event_EventHandle'$1_staking_contract_DistributeEvent''(bytes: Vec (int)): bool;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserializable'$1_event_EventHandle'$1_staking_contract_DistributeEvent''(bytes);
$IsValid'bool'($$res)));

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:11:9+47
function  $1_from_bcs_deserializable'$1_event_EventHandle'$1_staking_contract_RequestCommissionEvent''(bytes: Vec (int)): bool;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserializable'$1_event_EventHandle'$1_staking_contract_RequestCommissionEvent''(bytes);
$IsValid'bool'($$res)));

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:11:9+47
function  $1_from_bcs_deserializable'$1_event_EventHandle'$1_staking_contract_ResetLockupEvent''(bytes: Vec (int)): bool;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserializable'$1_event_EventHandle'$1_staking_contract_ResetLockupEvent''(bytes);
$IsValid'bool'($$res)));

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:11:9+47
function  $1_from_bcs_deserializable'$1_event_EventHandle'$1_staking_contract_SwitchOperatorEvent''(bytes: Vec (int)): bool;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserializable'$1_event_EventHandle'$1_staking_contract_SwitchOperatorEvent''(bytes);
$IsValid'bool'($$res)));

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:11:9+47
function  $1_from_bcs_deserializable'$1_event_EventHandle'$1_staking_contract_UpdateVoterEvent''(bytes: Vec (int)): bool;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserializable'$1_event_EventHandle'$1_staking_contract_UpdateVoterEvent''(bytes);
$IsValid'bool'($$res)));

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:11:9+47
function  $1_from_bcs_deserializable'$1_account_SignerCapability'(bytes: Vec (int)): bool;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserializable'$1_account_SignerCapability'(bytes);
$IsValid'bool'($$res)));

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:11:9+47
function  $1_from_bcs_deserializable'$1_aggregator_Aggregator'(bytes: Vec (int)): bool;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserializable'$1_aggregator_Aggregator'(bytes);
$IsValid'bool'($$res)));

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:11:9+47
function  $1_from_bcs_deserializable'$1_optional_aggregator_Integer'(bytes: Vec (int)): bool;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserializable'$1_optional_aggregator_Integer'(bytes);
$IsValid'bool'($$res)));

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:11:9+47
function  $1_from_bcs_deserializable'$1_optional_aggregator_OptionalAggregator'(bytes: Vec (int)): bool;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserializable'$1_optional_aggregator_OptionalAggregator'(bytes);
$IsValid'bool'($$res)));

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:11:9+47
function  $1_from_bcs_deserializable'$1_coin_Coin'$1_aptos_coin_AptosCoin''(bytes: Vec (int)): bool;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserializable'$1_coin_Coin'$1_aptos_coin_AptosCoin''(bytes);
$IsValid'bool'($$res)));

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:11:9+47
function  $1_from_bcs_deserializable'$1_coin_CoinInfo'$1_aptos_coin_AptosCoin''(bytes: Vec (int)): bool;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserializable'$1_coin_CoinInfo'$1_aptos_coin_AptosCoin''(bytes);
$IsValid'bool'($$res)));

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:11:9+47
function  $1_from_bcs_deserializable'$1_coin_Ghost$supply'$1_aptos_coin_AptosCoin''(bytes: Vec (int)): bool;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserializable'$1_coin_Ghost$supply'$1_aptos_coin_AptosCoin''(bytes);
$IsValid'bool'($$res)));

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:11:9+47
function  $1_from_bcs_deserializable'$1_coin_Ghost$aggregate_supply'$1_aptos_coin_AptosCoin''(bytes: Vec (int)): bool;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserializable'$1_coin_Ghost$aggregate_supply'$1_aptos_coin_AptosCoin''(bytes);
$IsValid'bool'($$res)));

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:11:9+47
function  $1_from_bcs_deserializable'$1_aptos_coin_AptosCoin'(bytes: Vec (int)): bool;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserializable'$1_aptos_coin_AptosCoin'(bytes);
$IsValid'bool'($$res)));

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:11:9+47
function  $1_from_bcs_deserializable'$1_simple_map_SimpleMap'address_u64''(bytes: Vec (int)): bool;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserializable'$1_simple_map_SimpleMap'address_u64''(bytes);
$IsValid'bool'($$res)));

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:11:9+47
function  $1_from_bcs_deserializable'$1_simple_map_SimpleMap'address_$1_staking_contract_StakingContract''(bytes: Vec (int)): bool;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserializable'$1_simple_map_SimpleMap'address_$1_staking_contract_StakingContract''(bytes);
$IsValid'bool'($$res)));

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:11:9+47
function  $1_from_bcs_deserializable'$1_stake_OwnerCapability'(bytes: Vec (int)): bool;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserializable'$1_stake_OwnerCapability'(bytes);
$IsValid'bool'($$res)));

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:11:9+47
function  $1_from_bcs_deserializable'$1_stake_StakePool'(bytes: Vec (int)): bool;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserializable'$1_stake_StakePool'(bytes);
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
function  $1_from_bcs_deserializable'$1_pool_u64_Pool'(bytes: Vec (int)): bool;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserializable'$1_pool_u64_Pool'(bytes);
$IsValid'bool'($$res)));

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:11:9+47
function  $1_from_bcs_deserializable'$1_staking_contract_StakingContract'(bytes: Vec (int)): bool;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserializable'$1_staking_contract_StakingContract'(bytes);
$IsValid'bool'($$res)));

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:11:9+47
function  $1_from_bcs_deserializable'$1_staking_contract_Store'(bytes: Vec (int)): bool;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserializable'$1_staking_contract_Store'(bytes);
$IsValid'bool'($$res)));

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:11:9+47
function  $1_from_bcs_deserializable'#0'(bytes: Vec (int)): bool;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserializable'#0'(bytes);
$IsValid'bool'($$res)));

// struct event::EventHandle<stake::AddStakeEvent> at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/event.move:16:5+224
type {:datatype} $1_event_EventHandle'$1_stake_AddStakeEvent';
function {:constructor} $1_event_EventHandle'$1_stake_AddStakeEvent'($counter: int, $guid: $1_guid_GUID): $1_event_EventHandle'$1_stake_AddStakeEvent';
function {:inline} $Update'$1_event_EventHandle'$1_stake_AddStakeEvent''_counter(s: $1_event_EventHandle'$1_stake_AddStakeEvent', x: int): $1_event_EventHandle'$1_stake_AddStakeEvent' {
    $1_event_EventHandle'$1_stake_AddStakeEvent'(x, $guid#$1_event_EventHandle'$1_stake_AddStakeEvent'(s))
}
function {:inline} $Update'$1_event_EventHandle'$1_stake_AddStakeEvent''_guid(s: $1_event_EventHandle'$1_stake_AddStakeEvent', x: $1_guid_GUID): $1_event_EventHandle'$1_stake_AddStakeEvent' {
    $1_event_EventHandle'$1_stake_AddStakeEvent'($counter#$1_event_EventHandle'$1_stake_AddStakeEvent'(s), x)
}
function $IsValid'$1_event_EventHandle'$1_stake_AddStakeEvent''(s: $1_event_EventHandle'$1_stake_AddStakeEvent'): bool {
    $IsValid'u64'($counter#$1_event_EventHandle'$1_stake_AddStakeEvent'(s))
      && $IsValid'$1_guid_GUID'($guid#$1_event_EventHandle'$1_stake_AddStakeEvent'(s))
}
function {:inline} $IsEqual'$1_event_EventHandle'$1_stake_AddStakeEvent''(s1: $1_event_EventHandle'$1_stake_AddStakeEvent', s2: $1_event_EventHandle'$1_stake_AddStakeEvent'): bool {
    s1 == s2
}

// struct event::EventHandle<stake::DistributeRewardsEvent> at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/event.move:16:5+224
type {:datatype} $1_event_EventHandle'$1_stake_DistributeRewardsEvent';
function {:constructor} $1_event_EventHandle'$1_stake_DistributeRewardsEvent'($counter: int, $guid: $1_guid_GUID): $1_event_EventHandle'$1_stake_DistributeRewardsEvent';
function {:inline} $Update'$1_event_EventHandle'$1_stake_DistributeRewardsEvent''_counter(s: $1_event_EventHandle'$1_stake_DistributeRewardsEvent', x: int): $1_event_EventHandle'$1_stake_DistributeRewardsEvent' {
    $1_event_EventHandle'$1_stake_DistributeRewardsEvent'(x, $guid#$1_event_EventHandle'$1_stake_DistributeRewardsEvent'(s))
}
function {:inline} $Update'$1_event_EventHandle'$1_stake_DistributeRewardsEvent''_guid(s: $1_event_EventHandle'$1_stake_DistributeRewardsEvent', x: $1_guid_GUID): $1_event_EventHandle'$1_stake_DistributeRewardsEvent' {
    $1_event_EventHandle'$1_stake_DistributeRewardsEvent'($counter#$1_event_EventHandle'$1_stake_DistributeRewardsEvent'(s), x)
}
function $IsValid'$1_event_EventHandle'$1_stake_DistributeRewardsEvent''(s: $1_event_EventHandle'$1_stake_DistributeRewardsEvent'): bool {
    $IsValid'u64'($counter#$1_event_EventHandle'$1_stake_DistributeRewardsEvent'(s))
      && $IsValid'$1_guid_GUID'($guid#$1_event_EventHandle'$1_stake_DistributeRewardsEvent'(s))
}
function {:inline} $IsEqual'$1_event_EventHandle'$1_stake_DistributeRewardsEvent''(s1: $1_event_EventHandle'$1_stake_DistributeRewardsEvent', s2: $1_event_EventHandle'$1_stake_DistributeRewardsEvent'): bool {
    s1 == s2
}

// struct event::EventHandle<stake::IncreaseLockupEvent> at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/event.move:16:5+224
type {:datatype} $1_event_EventHandle'$1_stake_IncreaseLockupEvent';
function {:constructor} $1_event_EventHandle'$1_stake_IncreaseLockupEvent'($counter: int, $guid: $1_guid_GUID): $1_event_EventHandle'$1_stake_IncreaseLockupEvent';
function {:inline} $Update'$1_event_EventHandle'$1_stake_IncreaseLockupEvent''_counter(s: $1_event_EventHandle'$1_stake_IncreaseLockupEvent', x: int): $1_event_EventHandle'$1_stake_IncreaseLockupEvent' {
    $1_event_EventHandle'$1_stake_IncreaseLockupEvent'(x, $guid#$1_event_EventHandle'$1_stake_IncreaseLockupEvent'(s))
}
function {:inline} $Update'$1_event_EventHandle'$1_stake_IncreaseLockupEvent''_guid(s: $1_event_EventHandle'$1_stake_IncreaseLockupEvent', x: $1_guid_GUID): $1_event_EventHandle'$1_stake_IncreaseLockupEvent' {
    $1_event_EventHandle'$1_stake_IncreaseLockupEvent'($counter#$1_event_EventHandle'$1_stake_IncreaseLockupEvent'(s), x)
}
function $IsValid'$1_event_EventHandle'$1_stake_IncreaseLockupEvent''(s: $1_event_EventHandle'$1_stake_IncreaseLockupEvent'): bool {
    $IsValid'u64'($counter#$1_event_EventHandle'$1_stake_IncreaseLockupEvent'(s))
      && $IsValid'$1_guid_GUID'($guid#$1_event_EventHandle'$1_stake_IncreaseLockupEvent'(s))
}
function {:inline} $IsEqual'$1_event_EventHandle'$1_stake_IncreaseLockupEvent''(s1: $1_event_EventHandle'$1_stake_IncreaseLockupEvent', s2: $1_event_EventHandle'$1_stake_IncreaseLockupEvent'): bool {
    s1 == s2
}

// struct event::EventHandle<stake::JoinValidatorSetEvent> at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/event.move:16:5+224
type {:datatype} $1_event_EventHandle'$1_stake_JoinValidatorSetEvent';
function {:constructor} $1_event_EventHandle'$1_stake_JoinValidatorSetEvent'($counter: int, $guid: $1_guid_GUID): $1_event_EventHandle'$1_stake_JoinValidatorSetEvent';
function {:inline} $Update'$1_event_EventHandle'$1_stake_JoinValidatorSetEvent''_counter(s: $1_event_EventHandle'$1_stake_JoinValidatorSetEvent', x: int): $1_event_EventHandle'$1_stake_JoinValidatorSetEvent' {
    $1_event_EventHandle'$1_stake_JoinValidatorSetEvent'(x, $guid#$1_event_EventHandle'$1_stake_JoinValidatorSetEvent'(s))
}
function {:inline} $Update'$1_event_EventHandle'$1_stake_JoinValidatorSetEvent''_guid(s: $1_event_EventHandle'$1_stake_JoinValidatorSetEvent', x: $1_guid_GUID): $1_event_EventHandle'$1_stake_JoinValidatorSetEvent' {
    $1_event_EventHandle'$1_stake_JoinValidatorSetEvent'($counter#$1_event_EventHandle'$1_stake_JoinValidatorSetEvent'(s), x)
}
function $IsValid'$1_event_EventHandle'$1_stake_JoinValidatorSetEvent''(s: $1_event_EventHandle'$1_stake_JoinValidatorSetEvent'): bool {
    $IsValid'u64'($counter#$1_event_EventHandle'$1_stake_JoinValidatorSetEvent'(s))
      && $IsValid'$1_guid_GUID'($guid#$1_event_EventHandle'$1_stake_JoinValidatorSetEvent'(s))
}
function {:inline} $IsEqual'$1_event_EventHandle'$1_stake_JoinValidatorSetEvent''(s1: $1_event_EventHandle'$1_stake_JoinValidatorSetEvent', s2: $1_event_EventHandle'$1_stake_JoinValidatorSetEvent'): bool {
    s1 == s2
}

// struct event::EventHandle<stake::LeaveValidatorSetEvent> at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/event.move:16:5+224
type {:datatype} $1_event_EventHandle'$1_stake_LeaveValidatorSetEvent';
function {:constructor} $1_event_EventHandle'$1_stake_LeaveValidatorSetEvent'($counter: int, $guid: $1_guid_GUID): $1_event_EventHandle'$1_stake_LeaveValidatorSetEvent';
function {:inline} $Update'$1_event_EventHandle'$1_stake_LeaveValidatorSetEvent''_counter(s: $1_event_EventHandle'$1_stake_LeaveValidatorSetEvent', x: int): $1_event_EventHandle'$1_stake_LeaveValidatorSetEvent' {
    $1_event_EventHandle'$1_stake_LeaveValidatorSetEvent'(x, $guid#$1_event_EventHandle'$1_stake_LeaveValidatorSetEvent'(s))
}
function {:inline} $Update'$1_event_EventHandle'$1_stake_LeaveValidatorSetEvent''_guid(s: $1_event_EventHandle'$1_stake_LeaveValidatorSetEvent', x: $1_guid_GUID): $1_event_EventHandle'$1_stake_LeaveValidatorSetEvent' {
    $1_event_EventHandle'$1_stake_LeaveValidatorSetEvent'($counter#$1_event_EventHandle'$1_stake_LeaveValidatorSetEvent'(s), x)
}
function $IsValid'$1_event_EventHandle'$1_stake_LeaveValidatorSetEvent''(s: $1_event_EventHandle'$1_stake_LeaveValidatorSetEvent'): bool {
    $IsValid'u64'($counter#$1_event_EventHandle'$1_stake_LeaveValidatorSetEvent'(s))
      && $IsValid'$1_guid_GUID'($guid#$1_event_EventHandle'$1_stake_LeaveValidatorSetEvent'(s))
}
function {:inline} $IsEqual'$1_event_EventHandle'$1_stake_LeaveValidatorSetEvent''(s1: $1_event_EventHandle'$1_stake_LeaveValidatorSetEvent', s2: $1_event_EventHandle'$1_stake_LeaveValidatorSetEvent'): bool {
    s1 == s2
}

// struct event::EventHandle<stake::ReactivateStakeEvent> at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/event.move:16:5+224
type {:datatype} $1_event_EventHandle'$1_stake_ReactivateStakeEvent';
function {:constructor} $1_event_EventHandle'$1_stake_ReactivateStakeEvent'($counter: int, $guid: $1_guid_GUID): $1_event_EventHandle'$1_stake_ReactivateStakeEvent';
function {:inline} $Update'$1_event_EventHandle'$1_stake_ReactivateStakeEvent''_counter(s: $1_event_EventHandle'$1_stake_ReactivateStakeEvent', x: int): $1_event_EventHandle'$1_stake_ReactivateStakeEvent' {
    $1_event_EventHandle'$1_stake_ReactivateStakeEvent'(x, $guid#$1_event_EventHandle'$1_stake_ReactivateStakeEvent'(s))
}
function {:inline} $Update'$1_event_EventHandle'$1_stake_ReactivateStakeEvent''_guid(s: $1_event_EventHandle'$1_stake_ReactivateStakeEvent', x: $1_guid_GUID): $1_event_EventHandle'$1_stake_ReactivateStakeEvent' {
    $1_event_EventHandle'$1_stake_ReactivateStakeEvent'($counter#$1_event_EventHandle'$1_stake_ReactivateStakeEvent'(s), x)
}
function $IsValid'$1_event_EventHandle'$1_stake_ReactivateStakeEvent''(s: $1_event_EventHandle'$1_stake_ReactivateStakeEvent'): bool {
    $IsValid'u64'($counter#$1_event_EventHandle'$1_stake_ReactivateStakeEvent'(s))
      && $IsValid'$1_guid_GUID'($guid#$1_event_EventHandle'$1_stake_ReactivateStakeEvent'(s))
}
function {:inline} $IsEqual'$1_event_EventHandle'$1_stake_ReactivateStakeEvent''(s1: $1_event_EventHandle'$1_stake_ReactivateStakeEvent', s2: $1_event_EventHandle'$1_stake_ReactivateStakeEvent'): bool {
    s1 == s2
}

// struct event::EventHandle<stake::RegisterValidatorCandidateEvent> at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/event.move:16:5+224
type {:datatype} $1_event_EventHandle'$1_stake_RegisterValidatorCandidateEvent';
function {:constructor} $1_event_EventHandle'$1_stake_RegisterValidatorCandidateEvent'($counter: int, $guid: $1_guid_GUID): $1_event_EventHandle'$1_stake_RegisterValidatorCandidateEvent';
function {:inline} $Update'$1_event_EventHandle'$1_stake_RegisterValidatorCandidateEvent''_counter(s: $1_event_EventHandle'$1_stake_RegisterValidatorCandidateEvent', x: int): $1_event_EventHandle'$1_stake_RegisterValidatorCandidateEvent' {
    $1_event_EventHandle'$1_stake_RegisterValidatorCandidateEvent'(x, $guid#$1_event_EventHandle'$1_stake_RegisterValidatorCandidateEvent'(s))
}
function {:inline} $Update'$1_event_EventHandle'$1_stake_RegisterValidatorCandidateEvent''_guid(s: $1_event_EventHandle'$1_stake_RegisterValidatorCandidateEvent', x: $1_guid_GUID): $1_event_EventHandle'$1_stake_RegisterValidatorCandidateEvent' {
    $1_event_EventHandle'$1_stake_RegisterValidatorCandidateEvent'($counter#$1_event_EventHandle'$1_stake_RegisterValidatorCandidateEvent'(s), x)
}
function $IsValid'$1_event_EventHandle'$1_stake_RegisterValidatorCandidateEvent''(s: $1_event_EventHandle'$1_stake_RegisterValidatorCandidateEvent'): bool {
    $IsValid'u64'($counter#$1_event_EventHandle'$1_stake_RegisterValidatorCandidateEvent'(s))
      && $IsValid'$1_guid_GUID'($guid#$1_event_EventHandle'$1_stake_RegisterValidatorCandidateEvent'(s))
}
function {:inline} $IsEqual'$1_event_EventHandle'$1_stake_RegisterValidatorCandidateEvent''(s1: $1_event_EventHandle'$1_stake_RegisterValidatorCandidateEvent', s2: $1_event_EventHandle'$1_stake_RegisterValidatorCandidateEvent'): bool {
    s1 == s2
}

// struct event::EventHandle<stake::RotateConsensusKeyEvent> at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/event.move:16:5+224
type {:datatype} $1_event_EventHandle'$1_stake_RotateConsensusKeyEvent';
function {:constructor} $1_event_EventHandle'$1_stake_RotateConsensusKeyEvent'($counter: int, $guid: $1_guid_GUID): $1_event_EventHandle'$1_stake_RotateConsensusKeyEvent';
function {:inline} $Update'$1_event_EventHandle'$1_stake_RotateConsensusKeyEvent''_counter(s: $1_event_EventHandle'$1_stake_RotateConsensusKeyEvent', x: int): $1_event_EventHandle'$1_stake_RotateConsensusKeyEvent' {
    $1_event_EventHandle'$1_stake_RotateConsensusKeyEvent'(x, $guid#$1_event_EventHandle'$1_stake_RotateConsensusKeyEvent'(s))
}
function {:inline} $Update'$1_event_EventHandle'$1_stake_RotateConsensusKeyEvent''_guid(s: $1_event_EventHandle'$1_stake_RotateConsensusKeyEvent', x: $1_guid_GUID): $1_event_EventHandle'$1_stake_RotateConsensusKeyEvent' {
    $1_event_EventHandle'$1_stake_RotateConsensusKeyEvent'($counter#$1_event_EventHandle'$1_stake_RotateConsensusKeyEvent'(s), x)
}
function $IsValid'$1_event_EventHandle'$1_stake_RotateConsensusKeyEvent''(s: $1_event_EventHandle'$1_stake_RotateConsensusKeyEvent'): bool {
    $IsValid'u64'($counter#$1_event_EventHandle'$1_stake_RotateConsensusKeyEvent'(s))
      && $IsValid'$1_guid_GUID'($guid#$1_event_EventHandle'$1_stake_RotateConsensusKeyEvent'(s))
}
function {:inline} $IsEqual'$1_event_EventHandle'$1_stake_RotateConsensusKeyEvent''(s1: $1_event_EventHandle'$1_stake_RotateConsensusKeyEvent', s2: $1_event_EventHandle'$1_stake_RotateConsensusKeyEvent'): bool {
    s1 == s2
}

// struct event::EventHandle<stake::SetOperatorEvent> at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/event.move:16:5+224
type {:datatype} $1_event_EventHandle'$1_stake_SetOperatorEvent';
function {:constructor} $1_event_EventHandle'$1_stake_SetOperatorEvent'($counter: int, $guid: $1_guid_GUID): $1_event_EventHandle'$1_stake_SetOperatorEvent';
function {:inline} $Update'$1_event_EventHandle'$1_stake_SetOperatorEvent''_counter(s: $1_event_EventHandle'$1_stake_SetOperatorEvent', x: int): $1_event_EventHandle'$1_stake_SetOperatorEvent' {
    $1_event_EventHandle'$1_stake_SetOperatorEvent'(x, $guid#$1_event_EventHandle'$1_stake_SetOperatorEvent'(s))
}
function {:inline} $Update'$1_event_EventHandle'$1_stake_SetOperatorEvent''_guid(s: $1_event_EventHandle'$1_stake_SetOperatorEvent', x: $1_guid_GUID): $1_event_EventHandle'$1_stake_SetOperatorEvent' {
    $1_event_EventHandle'$1_stake_SetOperatorEvent'($counter#$1_event_EventHandle'$1_stake_SetOperatorEvent'(s), x)
}
function $IsValid'$1_event_EventHandle'$1_stake_SetOperatorEvent''(s: $1_event_EventHandle'$1_stake_SetOperatorEvent'): bool {
    $IsValid'u64'($counter#$1_event_EventHandle'$1_stake_SetOperatorEvent'(s))
      && $IsValid'$1_guid_GUID'($guid#$1_event_EventHandle'$1_stake_SetOperatorEvent'(s))
}
function {:inline} $IsEqual'$1_event_EventHandle'$1_stake_SetOperatorEvent''(s1: $1_event_EventHandle'$1_stake_SetOperatorEvent', s2: $1_event_EventHandle'$1_stake_SetOperatorEvent'): bool {
    s1 == s2
}

// struct event::EventHandle<stake::UnlockStakeEvent> at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/event.move:16:5+224
type {:datatype} $1_event_EventHandle'$1_stake_UnlockStakeEvent';
function {:constructor} $1_event_EventHandle'$1_stake_UnlockStakeEvent'($counter: int, $guid: $1_guid_GUID): $1_event_EventHandle'$1_stake_UnlockStakeEvent';
function {:inline} $Update'$1_event_EventHandle'$1_stake_UnlockStakeEvent''_counter(s: $1_event_EventHandle'$1_stake_UnlockStakeEvent', x: int): $1_event_EventHandle'$1_stake_UnlockStakeEvent' {
    $1_event_EventHandle'$1_stake_UnlockStakeEvent'(x, $guid#$1_event_EventHandle'$1_stake_UnlockStakeEvent'(s))
}
function {:inline} $Update'$1_event_EventHandle'$1_stake_UnlockStakeEvent''_guid(s: $1_event_EventHandle'$1_stake_UnlockStakeEvent', x: $1_guid_GUID): $1_event_EventHandle'$1_stake_UnlockStakeEvent' {
    $1_event_EventHandle'$1_stake_UnlockStakeEvent'($counter#$1_event_EventHandle'$1_stake_UnlockStakeEvent'(s), x)
}
function $IsValid'$1_event_EventHandle'$1_stake_UnlockStakeEvent''(s: $1_event_EventHandle'$1_stake_UnlockStakeEvent'): bool {
    $IsValid'u64'($counter#$1_event_EventHandle'$1_stake_UnlockStakeEvent'(s))
      && $IsValid'$1_guid_GUID'($guid#$1_event_EventHandle'$1_stake_UnlockStakeEvent'(s))
}
function {:inline} $IsEqual'$1_event_EventHandle'$1_stake_UnlockStakeEvent''(s1: $1_event_EventHandle'$1_stake_UnlockStakeEvent', s2: $1_event_EventHandle'$1_stake_UnlockStakeEvent'): bool {
    s1 == s2
}

// struct event::EventHandle<stake::UpdateNetworkAndFullnodeAddressesEvent> at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/event.move:16:5+224
type {:datatype} $1_event_EventHandle'$1_stake_UpdateNetworkAndFullnodeAddressesEvent';
function {:constructor} $1_event_EventHandle'$1_stake_UpdateNetworkAndFullnodeAddressesEvent'($counter: int, $guid: $1_guid_GUID): $1_event_EventHandle'$1_stake_UpdateNetworkAndFullnodeAddressesEvent';
function {:inline} $Update'$1_event_EventHandle'$1_stake_UpdateNetworkAndFullnodeAddressesEvent''_counter(s: $1_event_EventHandle'$1_stake_UpdateNetworkAndFullnodeAddressesEvent', x: int): $1_event_EventHandle'$1_stake_UpdateNetworkAndFullnodeAddressesEvent' {
    $1_event_EventHandle'$1_stake_UpdateNetworkAndFullnodeAddressesEvent'(x, $guid#$1_event_EventHandle'$1_stake_UpdateNetworkAndFullnodeAddressesEvent'(s))
}
function {:inline} $Update'$1_event_EventHandle'$1_stake_UpdateNetworkAndFullnodeAddressesEvent''_guid(s: $1_event_EventHandle'$1_stake_UpdateNetworkAndFullnodeAddressesEvent', x: $1_guid_GUID): $1_event_EventHandle'$1_stake_UpdateNetworkAndFullnodeAddressesEvent' {
    $1_event_EventHandle'$1_stake_UpdateNetworkAndFullnodeAddressesEvent'($counter#$1_event_EventHandle'$1_stake_UpdateNetworkAndFullnodeAddressesEvent'(s), x)
}
function $IsValid'$1_event_EventHandle'$1_stake_UpdateNetworkAndFullnodeAddressesEvent''(s: $1_event_EventHandle'$1_stake_UpdateNetworkAndFullnodeAddressesEvent'): bool {
    $IsValid'u64'($counter#$1_event_EventHandle'$1_stake_UpdateNetworkAndFullnodeAddressesEvent'(s))
      && $IsValid'$1_guid_GUID'($guid#$1_event_EventHandle'$1_stake_UpdateNetworkAndFullnodeAddressesEvent'(s))
}
function {:inline} $IsEqual'$1_event_EventHandle'$1_stake_UpdateNetworkAndFullnodeAddressesEvent''(s1: $1_event_EventHandle'$1_stake_UpdateNetworkAndFullnodeAddressesEvent', s2: $1_event_EventHandle'$1_stake_UpdateNetworkAndFullnodeAddressesEvent'): bool {
    s1 == s2
}

// struct event::EventHandle<stake::WithdrawStakeEvent> at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/event.move:16:5+224
type {:datatype} $1_event_EventHandle'$1_stake_WithdrawStakeEvent';
function {:constructor} $1_event_EventHandle'$1_stake_WithdrawStakeEvent'($counter: int, $guid: $1_guid_GUID): $1_event_EventHandle'$1_stake_WithdrawStakeEvent';
function {:inline} $Update'$1_event_EventHandle'$1_stake_WithdrawStakeEvent''_counter(s: $1_event_EventHandle'$1_stake_WithdrawStakeEvent', x: int): $1_event_EventHandle'$1_stake_WithdrawStakeEvent' {
    $1_event_EventHandle'$1_stake_WithdrawStakeEvent'(x, $guid#$1_event_EventHandle'$1_stake_WithdrawStakeEvent'(s))
}
function {:inline} $Update'$1_event_EventHandle'$1_stake_WithdrawStakeEvent''_guid(s: $1_event_EventHandle'$1_stake_WithdrawStakeEvent', x: $1_guid_GUID): $1_event_EventHandle'$1_stake_WithdrawStakeEvent' {
    $1_event_EventHandle'$1_stake_WithdrawStakeEvent'($counter#$1_event_EventHandle'$1_stake_WithdrawStakeEvent'(s), x)
}
function $IsValid'$1_event_EventHandle'$1_stake_WithdrawStakeEvent''(s: $1_event_EventHandle'$1_stake_WithdrawStakeEvent'): bool {
    $IsValid'u64'($counter#$1_event_EventHandle'$1_stake_WithdrawStakeEvent'(s))
      && $IsValid'$1_guid_GUID'($guid#$1_event_EventHandle'$1_stake_WithdrawStakeEvent'(s))
}
function {:inline} $IsEqual'$1_event_EventHandle'$1_stake_WithdrawStakeEvent''(s1: $1_event_EventHandle'$1_stake_WithdrawStakeEvent', s2: $1_event_EventHandle'$1_stake_WithdrawStakeEvent'): bool {
    s1 == s2
}

// struct event::EventHandle<staking_contract::AddStakeEvent> at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/event.move:16:5+224
type {:datatype} $1_event_EventHandle'$1_staking_contract_AddStakeEvent';
function {:constructor} $1_event_EventHandle'$1_staking_contract_AddStakeEvent'($counter: int, $guid: $1_guid_GUID): $1_event_EventHandle'$1_staking_contract_AddStakeEvent';
function {:inline} $Update'$1_event_EventHandle'$1_staking_contract_AddStakeEvent''_counter(s: $1_event_EventHandle'$1_staking_contract_AddStakeEvent', x: int): $1_event_EventHandle'$1_staking_contract_AddStakeEvent' {
    $1_event_EventHandle'$1_staking_contract_AddStakeEvent'(x, $guid#$1_event_EventHandle'$1_staking_contract_AddStakeEvent'(s))
}
function {:inline} $Update'$1_event_EventHandle'$1_staking_contract_AddStakeEvent''_guid(s: $1_event_EventHandle'$1_staking_contract_AddStakeEvent', x: $1_guid_GUID): $1_event_EventHandle'$1_staking_contract_AddStakeEvent' {
    $1_event_EventHandle'$1_staking_contract_AddStakeEvent'($counter#$1_event_EventHandle'$1_staking_contract_AddStakeEvent'(s), x)
}
function $IsValid'$1_event_EventHandle'$1_staking_contract_AddStakeEvent''(s: $1_event_EventHandle'$1_staking_contract_AddStakeEvent'): bool {
    $IsValid'u64'($counter#$1_event_EventHandle'$1_staking_contract_AddStakeEvent'(s))
      && $IsValid'$1_guid_GUID'($guid#$1_event_EventHandle'$1_staking_contract_AddStakeEvent'(s))
}
function {:inline} $IsEqual'$1_event_EventHandle'$1_staking_contract_AddStakeEvent''(s1: $1_event_EventHandle'$1_staking_contract_AddStakeEvent', s2: $1_event_EventHandle'$1_staking_contract_AddStakeEvent'): bool {
    s1 == s2
}

// struct event::EventHandle<staking_contract::UnlockStakeEvent> at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/event.move:16:5+224
type {:datatype} $1_event_EventHandle'$1_staking_contract_UnlockStakeEvent';
function {:constructor} $1_event_EventHandle'$1_staking_contract_UnlockStakeEvent'($counter: int, $guid: $1_guid_GUID): $1_event_EventHandle'$1_staking_contract_UnlockStakeEvent';
function {:inline} $Update'$1_event_EventHandle'$1_staking_contract_UnlockStakeEvent''_counter(s: $1_event_EventHandle'$1_staking_contract_UnlockStakeEvent', x: int): $1_event_EventHandle'$1_staking_contract_UnlockStakeEvent' {
    $1_event_EventHandle'$1_staking_contract_UnlockStakeEvent'(x, $guid#$1_event_EventHandle'$1_staking_contract_UnlockStakeEvent'(s))
}
function {:inline} $Update'$1_event_EventHandle'$1_staking_contract_UnlockStakeEvent''_guid(s: $1_event_EventHandle'$1_staking_contract_UnlockStakeEvent', x: $1_guid_GUID): $1_event_EventHandle'$1_staking_contract_UnlockStakeEvent' {
    $1_event_EventHandle'$1_staking_contract_UnlockStakeEvent'($counter#$1_event_EventHandle'$1_staking_contract_UnlockStakeEvent'(s), x)
}
function $IsValid'$1_event_EventHandle'$1_staking_contract_UnlockStakeEvent''(s: $1_event_EventHandle'$1_staking_contract_UnlockStakeEvent'): bool {
    $IsValid'u64'($counter#$1_event_EventHandle'$1_staking_contract_UnlockStakeEvent'(s))
      && $IsValid'$1_guid_GUID'($guid#$1_event_EventHandle'$1_staking_contract_UnlockStakeEvent'(s))
}
function {:inline} $IsEqual'$1_event_EventHandle'$1_staking_contract_UnlockStakeEvent''(s1: $1_event_EventHandle'$1_staking_contract_UnlockStakeEvent', s2: $1_event_EventHandle'$1_staking_contract_UnlockStakeEvent'): bool {
    s1 == s2
}

// struct event::EventHandle<staking_contract::AddDistributionEvent> at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/event.move:16:5+224
type {:datatype} $1_event_EventHandle'$1_staking_contract_AddDistributionEvent';
function {:constructor} $1_event_EventHandle'$1_staking_contract_AddDistributionEvent'($counter: int, $guid: $1_guid_GUID): $1_event_EventHandle'$1_staking_contract_AddDistributionEvent';
function {:inline} $Update'$1_event_EventHandle'$1_staking_contract_AddDistributionEvent''_counter(s: $1_event_EventHandle'$1_staking_contract_AddDistributionEvent', x: int): $1_event_EventHandle'$1_staking_contract_AddDistributionEvent' {
    $1_event_EventHandle'$1_staking_contract_AddDistributionEvent'(x, $guid#$1_event_EventHandle'$1_staking_contract_AddDistributionEvent'(s))
}
function {:inline} $Update'$1_event_EventHandle'$1_staking_contract_AddDistributionEvent''_guid(s: $1_event_EventHandle'$1_staking_contract_AddDistributionEvent', x: $1_guid_GUID): $1_event_EventHandle'$1_staking_contract_AddDistributionEvent' {
    $1_event_EventHandle'$1_staking_contract_AddDistributionEvent'($counter#$1_event_EventHandle'$1_staking_contract_AddDistributionEvent'(s), x)
}
function $IsValid'$1_event_EventHandle'$1_staking_contract_AddDistributionEvent''(s: $1_event_EventHandle'$1_staking_contract_AddDistributionEvent'): bool {
    $IsValid'u64'($counter#$1_event_EventHandle'$1_staking_contract_AddDistributionEvent'(s))
      && $IsValid'$1_guid_GUID'($guid#$1_event_EventHandle'$1_staking_contract_AddDistributionEvent'(s))
}
function {:inline} $IsEqual'$1_event_EventHandle'$1_staking_contract_AddDistributionEvent''(s1: $1_event_EventHandle'$1_staking_contract_AddDistributionEvent', s2: $1_event_EventHandle'$1_staking_contract_AddDistributionEvent'): bool {
    s1 == s2
}

// struct event::EventHandle<staking_contract::CreateStakingContractEvent> at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/event.move:16:5+224
type {:datatype} $1_event_EventHandle'$1_staking_contract_CreateStakingContractEvent';
function {:constructor} $1_event_EventHandle'$1_staking_contract_CreateStakingContractEvent'($counter: int, $guid: $1_guid_GUID): $1_event_EventHandle'$1_staking_contract_CreateStakingContractEvent';
function {:inline} $Update'$1_event_EventHandle'$1_staking_contract_CreateStakingContractEvent''_counter(s: $1_event_EventHandle'$1_staking_contract_CreateStakingContractEvent', x: int): $1_event_EventHandle'$1_staking_contract_CreateStakingContractEvent' {
    $1_event_EventHandle'$1_staking_contract_CreateStakingContractEvent'(x, $guid#$1_event_EventHandle'$1_staking_contract_CreateStakingContractEvent'(s))
}
function {:inline} $Update'$1_event_EventHandle'$1_staking_contract_CreateStakingContractEvent''_guid(s: $1_event_EventHandle'$1_staking_contract_CreateStakingContractEvent', x: $1_guid_GUID): $1_event_EventHandle'$1_staking_contract_CreateStakingContractEvent' {
    $1_event_EventHandle'$1_staking_contract_CreateStakingContractEvent'($counter#$1_event_EventHandle'$1_staking_contract_CreateStakingContractEvent'(s), x)
}
function $IsValid'$1_event_EventHandle'$1_staking_contract_CreateStakingContractEvent''(s: $1_event_EventHandle'$1_staking_contract_CreateStakingContractEvent'): bool {
    $IsValid'u64'($counter#$1_event_EventHandle'$1_staking_contract_CreateStakingContractEvent'(s))
      && $IsValid'$1_guid_GUID'($guid#$1_event_EventHandle'$1_staking_contract_CreateStakingContractEvent'(s))
}
function {:inline} $IsEqual'$1_event_EventHandle'$1_staking_contract_CreateStakingContractEvent''(s1: $1_event_EventHandle'$1_staking_contract_CreateStakingContractEvent', s2: $1_event_EventHandle'$1_staking_contract_CreateStakingContractEvent'): bool {
    s1 == s2
}

// struct event::EventHandle<staking_contract::DistributeEvent> at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/event.move:16:5+224
type {:datatype} $1_event_EventHandle'$1_staking_contract_DistributeEvent';
function {:constructor} $1_event_EventHandle'$1_staking_contract_DistributeEvent'($counter: int, $guid: $1_guid_GUID): $1_event_EventHandle'$1_staking_contract_DistributeEvent';
function {:inline} $Update'$1_event_EventHandle'$1_staking_contract_DistributeEvent''_counter(s: $1_event_EventHandle'$1_staking_contract_DistributeEvent', x: int): $1_event_EventHandle'$1_staking_contract_DistributeEvent' {
    $1_event_EventHandle'$1_staking_contract_DistributeEvent'(x, $guid#$1_event_EventHandle'$1_staking_contract_DistributeEvent'(s))
}
function {:inline} $Update'$1_event_EventHandle'$1_staking_contract_DistributeEvent''_guid(s: $1_event_EventHandle'$1_staking_contract_DistributeEvent', x: $1_guid_GUID): $1_event_EventHandle'$1_staking_contract_DistributeEvent' {
    $1_event_EventHandle'$1_staking_contract_DistributeEvent'($counter#$1_event_EventHandle'$1_staking_contract_DistributeEvent'(s), x)
}
function $IsValid'$1_event_EventHandle'$1_staking_contract_DistributeEvent''(s: $1_event_EventHandle'$1_staking_contract_DistributeEvent'): bool {
    $IsValid'u64'($counter#$1_event_EventHandle'$1_staking_contract_DistributeEvent'(s))
      && $IsValid'$1_guid_GUID'($guid#$1_event_EventHandle'$1_staking_contract_DistributeEvent'(s))
}
function {:inline} $IsEqual'$1_event_EventHandle'$1_staking_contract_DistributeEvent''(s1: $1_event_EventHandle'$1_staking_contract_DistributeEvent', s2: $1_event_EventHandle'$1_staking_contract_DistributeEvent'): bool {
    s1 == s2
}

// struct event::EventHandle<staking_contract::RequestCommissionEvent> at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/event.move:16:5+224
type {:datatype} $1_event_EventHandle'$1_staking_contract_RequestCommissionEvent';
function {:constructor} $1_event_EventHandle'$1_staking_contract_RequestCommissionEvent'($counter: int, $guid: $1_guid_GUID): $1_event_EventHandle'$1_staking_contract_RequestCommissionEvent';
function {:inline} $Update'$1_event_EventHandle'$1_staking_contract_RequestCommissionEvent''_counter(s: $1_event_EventHandle'$1_staking_contract_RequestCommissionEvent', x: int): $1_event_EventHandle'$1_staking_contract_RequestCommissionEvent' {
    $1_event_EventHandle'$1_staking_contract_RequestCommissionEvent'(x, $guid#$1_event_EventHandle'$1_staking_contract_RequestCommissionEvent'(s))
}
function {:inline} $Update'$1_event_EventHandle'$1_staking_contract_RequestCommissionEvent''_guid(s: $1_event_EventHandle'$1_staking_contract_RequestCommissionEvent', x: $1_guid_GUID): $1_event_EventHandle'$1_staking_contract_RequestCommissionEvent' {
    $1_event_EventHandle'$1_staking_contract_RequestCommissionEvent'($counter#$1_event_EventHandle'$1_staking_contract_RequestCommissionEvent'(s), x)
}
function $IsValid'$1_event_EventHandle'$1_staking_contract_RequestCommissionEvent''(s: $1_event_EventHandle'$1_staking_contract_RequestCommissionEvent'): bool {
    $IsValid'u64'($counter#$1_event_EventHandle'$1_staking_contract_RequestCommissionEvent'(s))
      && $IsValid'$1_guid_GUID'($guid#$1_event_EventHandle'$1_staking_contract_RequestCommissionEvent'(s))
}
function {:inline} $IsEqual'$1_event_EventHandle'$1_staking_contract_RequestCommissionEvent''(s1: $1_event_EventHandle'$1_staking_contract_RequestCommissionEvent', s2: $1_event_EventHandle'$1_staking_contract_RequestCommissionEvent'): bool {
    s1 == s2
}

// struct event::EventHandle<staking_contract::ResetLockupEvent> at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/event.move:16:5+224
type {:datatype} $1_event_EventHandle'$1_staking_contract_ResetLockupEvent';
function {:constructor} $1_event_EventHandle'$1_staking_contract_ResetLockupEvent'($counter: int, $guid: $1_guid_GUID): $1_event_EventHandle'$1_staking_contract_ResetLockupEvent';
function {:inline} $Update'$1_event_EventHandle'$1_staking_contract_ResetLockupEvent''_counter(s: $1_event_EventHandle'$1_staking_contract_ResetLockupEvent', x: int): $1_event_EventHandle'$1_staking_contract_ResetLockupEvent' {
    $1_event_EventHandle'$1_staking_contract_ResetLockupEvent'(x, $guid#$1_event_EventHandle'$1_staking_contract_ResetLockupEvent'(s))
}
function {:inline} $Update'$1_event_EventHandle'$1_staking_contract_ResetLockupEvent''_guid(s: $1_event_EventHandle'$1_staking_contract_ResetLockupEvent', x: $1_guid_GUID): $1_event_EventHandle'$1_staking_contract_ResetLockupEvent' {
    $1_event_EventHandle'$1_staking_contract_ResetLockupEvent'($counter#$1_event_EventHandle'$1_staking_contract_ResetLockupEvent'(s), x)
}
function $IsValid'$1_event_EventHandle'$1_staking_contract_ResetLockupEvent''(s: $1_event_EventHandle'$1_staking_contract_ResetLockupEvent'): bool {
    $IsValid'u64'($counter#$1_event_EventHandle'$1_staking_contract_ResetLockupEvent'(s))
      && $IsValid'$1_guid_GUID'($guid#$1_event_EventHandle'$1_staking_contract_ResetLockupEvent'(s))
}
function {:inline} $IsEqual'$1_event_EventHandle'$1_staking_contract_ResetLockupEvent''(s1: $1_event_EventHandle'$1_staking_contract_ResetLockupEvent', s2: $1_event_EventHandle'$1_staking_contract_ResetLockupEvent'): bool {
    s1 == s2
}

// struct event::EventHandle<staking_contract::SwitchOperatorEvent> at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/event.move:16:5+224
type {:datatype} $1_event_EventHandle'$1_staking_contract_SwitchOperatorEvent';
function {:constructor} $1_event_EventHandle'$1_staking_contract_SwitchOperatorEvent'($counter: int, $guid: $1_guid_GUID): $1_event_EventHandle'$1_staking_contract_SwitchOperatorEvent';
function {:inline} $Update'$1_event_EventHandle'$1_staking_contract_SwitchOperatorEvent''_counter(s: $1_event_EventHandle'$1_staking_contract_SwitchOperatorEvent', x: int): $1_event_EventHandle'$1_staking_contract_SwitchOperatorEvent' {
    $1_event_EventHandle'$1_staking_contract_SwitchOperatorEvent'(x, $guid#$1_event_EventHandle'$1_staking_contract_SwitchOperatorEvent'(s))
}
function {:inline} $Update'$1_event_EventHandle'$1_staking_contract_SwitchOperatorEvent''_guid(s: $1_event_EventHandle'$1_staking_contract_SwitchOperatorEvent', x: $1_guid_GUID): $1_event_EventHandle'$1_staking_contract_SwitchOperatorEvent' {
    $1_event_EventHandle'$1_staking_contract_SwitchOperatorEvent'($counter#$1_event_EventHandle'$1_staking_contract_SwitchOperatorEvent'(s), x)
}
function $IsValid'$1_event_EventHandle'$1_staking_contract_SwitchOperatorEvent''(s: $1_event_EventHandle'$1_staking_contract_SwitchOperatorEvent'): bool {
    $IsValid'u64'($counter#$1_event_EventHandle'$1_staking_contract_SwitchOperatorEvent'(s))
      && $IsValid'$1_guid_GUID'($guid#$1_event_EventHandle'$1_staking_contract_SwitchOperatorEvent'(s))
}
function {:inline} $IsEqual'$1_event_EventHandle'$1_staking_contract_SwitchOperatorEvent''(s1: $1_event_EventHandle'$1_staking_contract_SwitchOperatorEvent', s2: $1_event_EventHandle'$1_staking_contract_SwitchOperatorEvent'): bool {
    s1 == s2
}

// struct event::EventHandle<staking_contract::UpdateVoterEvent> at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/event.move:16:5+224
type {:datatype} $1_event_EventHandle'$1_staking_contract_UpdateVoterEvent';
function {:constructor} $1_event_EventHandle'$1_staking_contract_UpdateVoterEvent'($counter: int, $guid: $1_guid_GUID): $1_event_EventHandle'$1_staking_contract_UpdateVoterEvent';
function {:inline} $Update'$1_event_EventHandle'$1_staking_contract_UpdateVoterEvent''_counter(s: $1_event_EventHandle'$1_staking_contract_UpdateVoterEvent', x: int): $1_event_EventHandle'$1_staking_contract_UpdateVoterEvent' {
    $1_event_EventHandle'$1_staking_contract_UpdateVoterEvent'(x, $guid#$1_event_EventHandle'$1_staking_contract_UpdateVoterEvent'(s))
}
function {:inline} $Update'$1_event_EventHandle'$1_staking_contract_UpdateVoterEvent''_guid(s: $1_event_EventHandle'$1_staking_contract_UpdateVoterEvent', x: $1_guid_GUID): $1_event_EventHandle'$1_staking_contract_UpdateVoterEvent' {
    $1_event_EventHandle'$1_staking_contract_UpdateVoterEvent'($counter#$1_event_EventHandle'$1_staking_contract_UpdateVoterEvent'(s), x)
}
function $IsValid'$1_event_EventHandle'$1_staking_contract_UpdateVoterEvent''(s: $1_event_EventHandle'$1_staking_contract_UpdateVoterEvent'): bool {
    $IsValid'u64'($counter#$1_event_EventHandle'$1_staking_contract_UpdateVoterEvent'(s))
      && $IsValid'$1_guid_GUID'($guid#$1_event_EventHandle'$1_staking_contract_UpdateVoterEvent'(s))
}
function {:inline} $IsEqual'$1_event_EventHandle'$1_staking_contract_UpdateVoterEvent''(s1: $1_event_EventHandle'$1_staking_contract_UpdateVoterEvent', s2: $1_event_EventHandle'$1_staking_contract_UpdateVoterEvent'): bool {
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

// struct optional_aggregator::Integer at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aggregator/optional_aggregator.move:20:5+74
type {:datatype} $1_optional_aggregator_Integer;
function {:constructor} $1_optional_aggregator_Integer($value: int, $limit: int): $1_optional_aggregator_Integer;
function {:inline} $Update'$1_optional_aggregator_Integer'_value(s: $1_optional_aggregator_Integer, x: int): $1_optional_aggregator_Integer {
    $1_optional_aggregator_Integer(x, $limit#$1_optional_aggregator_Integer(s))
}
function {:inline} $Update'$1_optional_aggregator_Integer'_limit(s: $1_optional_aggregator_Integer, x: int): $1_optional_aggregator_Integer {
    $1_optional_aggregator_Integer($value#$1_optional_aggregator_Integer(s), x)
}
function $IsValid'$1_optional_aggregator_Integer'(s: $1_optional_aggregator_Integer): bool {
    $IsValid'u128'($value#$1_optional_aggregator_Integer(s))
      && $IsValid'u128'($limit#$1_optional_aggregator_Integer(s))
}
function {:inline} $IsEqual'$1_optional_aggregator_Integer'(s1: $1_optional_aggregator_Integer, s2: $1_optional_aggregator_Integer): bool {
    s1 == s2
}

// struct optional_aggregator::OptionalAggregator at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aggregator/optional_aggregator.move:64:5+175
type {:datatype} $1_optional_aggregator_OptionalAggregator;
function {:constructor} $1_optional_aggregator_OptionalAggregator($aggregator: $1_option_Option'$1_aggregator_Aggregator', $integer: $1_option_Option'$1_optional_aggregator_Integer'): $1_optional_aggregator_OptionalAggregator;
function {:inline} $Update'$1_optional_aggregator_OptionalAggregator'_aggregator(s: $1_optional_aggregator_OptionalAggregator, x: $1_option_Option'$1_aggregator_Aggregator'): $1_optional_aggregator_OptionalAggregator {
    $1_optional_aggregator_OptionalAggregator(x, $integer#$1_optional_aggregator_OptionalAggregator(s))
}
function {:inline} $Update'$1_optional_aggregator_OptionalAggregator'_integer(s: $1_optional_aggregator_OptionalAggregator, x: $1_option_Option'$1_optional_aggregator_Integer'): $1_optional_aggregator_OptionalAggregator {
    $1_optional_aggregator_OptionalAggregator($aggregator#$1_optional_aggregator_OptionalAggregator(s), x)
}
function $IsValid'$1_optional_aggregator_OptionalAggregator'(s: $1_optional_aggregator_OptionalAggregator): bool {
    $IsValid'$1_option_Option'$1_aggregator_Aggregator''($aggregator#$1_optional_aggregator_OptionalAggregator(s))
      && $IsValid'$1_option_Option'$1_optional_aggregator_Integer''($integer#$1_optional_aggregator_OptionalAggregator(s))
}
function {:inline} $IsEqual'$1_optional_aggregator_OptionalAggregator'(s1: $1_optional_aggregator_OptionalAggregator, s2: $1_optional_aggregator_OptionalAggregator): bool {
    $IsEqual'$1_option_Option'$1_aggregator_Aggregator''($aggregator#$1_optional_aggregator_OptionalAggregator(s1), $aggregator#$1_optional_aggregator_OptionalAggregator(s2))
    && $IsEqual'$1_option_Option'$1_optional_aggregator_Integer''($integer#$1_optional_aggregator_OptionalAggregator(s1), $integer#$1_optional_aggregator_OptionalAggregator(s2))}

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.move:566:5+81
function {:inline} $1_coin_$value'$1_aptos_coin_AptosCoin'(coin: $1_coin_Coin'$1_aptos_coin_AptosCoin'): int {
    $value#$1_coin_Coin'$1_aptos_coin_AptosCoin'(coin)
}

// struct coin::Coin<aptos_coin::AptosCoin> at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.move:74:5+112
type {:datatype} $1_coin_Coin'$1_aptos_coin_AptosCoin';
function {:constructor} $1_coin_Coin'$1_aptos_coin_AptosCoin'($value: int): $1_coin_Coin'$1_aptos_coin_AptosCoin';
function {:inline} $Update'$1_coin_Coin'$1_aptos_coin_AptosCoin''_value(s: $1_coin_Coin'$1_aptos_coin_AptosCoin', x: int): $1_coin_Coin'$1_aptos_coin_AptosCoin' {
    $1_coin_Coin'$1_aptos_coin_AptosCoin'(x)
}
function $IsValid'$1_coin_Coin'$1_aptos_coin_AptosCoin''(s: $1_coin_Coin'$1_aptos_coin_AptosCoin'): bool {
    $IsValid'u64'($value#$1_coin_Coin'$1_aptos_coin_AptosCoin'(s))
}
function {:inline} $IsEqual'$1_coin_Coin'$1_aptos_coin_AptosCoin''(s1: $1_coin_Coin'$1_aptos_coin_AptosCoin', s2: $1_coin_Coin'$1_aptos_coin_AptosCoin'): bool {
    s1 == s2
}

// struct coin::CoinInfo<aptos_coin::AptosCoin> at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.move:109:5+564
type {:datatype} $1_coin_CoinInfo'$1_aptos_coin_AptosCoin';
function {:constructor} $1_coin_CoinInfo'$1_aptos_coin_AptosCoin'($name: $1_string_String, $symbol: $1_string_String, $decimals: int, $supply: $1_option_Option'$1_optional_aggregator_OptionalAggregator'): $1_coin_CoinInfo'$1_aptos_coin_AptosCoin';
function {:inline} $Update'$1_coin_CoinInfo'$1_aptos_coin_AptosCoin''_name(s: $1_coin_CoinInfo'$1_aptos_coin_AptosCoin', x: $1_string_String): $1_coin_CoinInfo'$1_aptos_coin_AptosCoin' {
    $1_coin_CoinInfo'$1_aptos_coin_AptosCoin'(x, $symbol#$1_coin_CoinInfo'$1_aptos_coin_AptosCoin'(s), $decimals#$1_coin_CoinInfo'$1_aptos_coin_AptosCoin'(s), $supply#$1_coin_CoinInfo'$1_aptos_coin_AptosCoin'(s))
}
function {:inline} $Update'$1_coin_CoinInfo'$1_aptos_coin_AptosCoin''_symbol(s: $1_coin_CoinInfo'$1_aptos_coin_AptosCoin', x: $1_string_String): $1_coin_CoinInfo'$1_aptos_coin_AptosCoin' {
    $1_coin_CoinInfo'$1_aptos_coin_AptosCoin'($name#$1_coin_CoinInfo'$1_aptos_coin_AptosCoin'(s), x, $decimals#$1_coin_CoinInfo'$1_aptos_coin_AptosCoin'(s), $supply#$1_coin_CoinInfo'$1_aptos_coin_AptosCoin'(s))
}
function {:inline} $Update'$1_coin_CoinInfo'$1_aptos_coin_AptosCoin''_decimals(s: $1_coin_CoinInfo'$1_aptos_coin_AptosCoin', x: int): $1_coin_CoinInfo'$1_aptos_coin_AptosCoin' {
    $1_coin_CoinInfo'$1_aptos_coin_AptosCoin'($name#$1_coin_CoinInfo'$1_aptos_coin_AptosCoin'(s), $symbol#$1_coin_CoinInfo'$1_aptos_coin_AptosCoin'(s), x, $supply#$1_coin_CoinInfo'$1_aptos_coin_AptosCoin'(s))
}
function {:inline} $Update'$1_coin_CoinInfo'$1_aptos_coin_AptosCoin''_supply(s: $1_coin_CoinInfo'$1_aptos_coin_AptosCoin', x: $1_option_Option'$1_optional_aggregator_OptionalAggregator'): $1_coin_CoinInfo'$1_aptos_coin_AptosCoin' {
    $1_coin_CoinInfo'$1_aptos_coin_AptosCoin'($name#$1_coin_CoinInfo'$1_aptos_coin_AptosCoin'(s), $symbol#$1_coin_CoinInfo'$1_aptos_coin_AptosCoin'(s), $decimals#$1_coin_CoinInfo'$1_aptos_coin_AptosCoin'(s), x)
}
function $IsValid'$1_coin_CoinInfo'$1_aptos_coin_AptosCoin''(s: $1_coin_CoinInfo'$1_aptos_coin_AptosCoin'): bool {
    $IsValid'$1_string_String'($name#$1_coin_CoinInfo'$1_aptos_coin_AptosCoin'(s))
      && $IsValid'$1_string_String'($symbol#$1_coin_CoinInfo'$1_aptos_coin_AptosCoin'(s))
      && $IsValid'u8'($decimals#$1_coin_CoinInfo'$1_aptos_coin_AptosCoin'(s))
      && $IsValid'$1_option_Option'$1_optional_aggregator_OptionalAggregator''($supply#$1_coin_CoinInfo'$1_aptos_coin_AptosCoin'(s))
}
function {:inline} $IsEqual'$1_coin_CoinInfo'$1_aptos_coin_AptosCoin''(s1: $1_coin_CoinInfo'$1_aptos_coin_AptosCoin', s2: $1_coin_CoinInfo'$1_aptos_coin_AptosCoin'): bool {
    $IsEqual'$1_string_String'($name#$1_coin_CoinInfo'$1_aptos_coin_AptosCoin'(s1), $name#$1_coin_CoinInfo'$1_aptos_coin_AptosCoin'(s2))
    && $IsEqual'$1_string_String'($symbol#$1_coin_CoinInfo'$1_aptos_coin_AptosCoin'(s1), $symbol#$1_coin_CoinInfo'$1_aptos_coin_AptosCoin'(s2))
    && $IsEqual'u8'($decimals#$1_coin_CoinInfo'$1_aptos_coin_AptosCoin'(s1), $decimals#$1_coin_CoinInfo'$1_aptos_coin_AptosCoin'(s2))
    && $IsEqual'$1_option_Option'$1_optional_aggregator_OptionalAggregator''($supply#$1_coin_CoinInfo'$1_aptos_coin_AptosCoin'(s1), $supply#$1_coin_CoinInfo'$1_aptos_coin_AptosCoin'(s2))}
var $1_coin_CoinInfo'$1_aptos_coin_AptosCoin'_$memory: $Memory $1_coin_CoinInfo'$1_aptos_coin_AptosCoin';

// struct coin::Ghost$supply<aptos_coin::AptosCoin> at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.spec.move:4:9+29
type {:datatype} $1_coin_Ghost$supply'$1_aptos_coin_AptosCoin';
function {:constructor} $1_coin_Ghost$supply'$1_aptos_coin_AptosCoin'($v: int): $1_coin_Ghost$supply'$1_aptos_coin_AptosCoin';
function {:inline} $Update'$1_coin_Ghost$supply'$1_aptos_coin_AptosCoin''_v(s: $1_coin_Ghost$supply'$1_aptos_coin_AptosCoin', x: int): $1_coin_Ghost$supply'$1_aptos_coin_AptosCoin' {
    $1_coin_Ghost$supply'$1_aptos_coin_AptosCoin'(x)
}
function $IsValid'$1_coin_Ghost$supply'$1_aptos_coin_AptosCoin''(s: $1_coin_Ghost$supply'$1_aptos_coin_AptosCoin'): bool {
    $IsValid'num'($v#$1_coin_Ghost$supply'$1_aptos_coin_AptosCoin'(s))
}
function {:inline} $IsEqual'$1_coin_Ghost$supply'$1_aptos_coin_AptosCoin''(s1: $1_coin_Ghost$supply'$1_aptos_coin_AptosCoin', s2: $1_coin_Ghost$supply'$1_aptos_coin_AptosCoin'): bool {
    s1 == s2
}
var $1_coin_Ghost$supply'$1_aptos_coin_AptosCoin'_$memory: $Memory $1_coin_Ghost$supply'$1_aptos_coin_AptosCoin';

// struct coin::Ghost$aggregate_supply<aptos_coin::AptosCoin> at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.spec.move:5:9+39
type {:datatype} $1_coin_Ghost$aggregate_supply'$1_aptos_coin_AptosCoin';
function {:constructor} $1_coin_Ghost$aggregate_supply'$1_aptos_coin_AptosCoin'($v: int): $1_coin_Ghost$aggregate_supply'$1_aptos_coin_AptosCoin';
function {:inline} $Update'$1_coin_Ghost$aggregate_supply'$1_aptos_coin_AptosCoin''_v(s: $1_coin_Ghost$aggregate_supply'$1_aptos_coin_AptosCoin', x: int): $1_coin_Ghost$aggregate_supply'$1_aptos_coin_AptosCoin' {
    $1_coin_Ghost$aggregate_supply'$1_aptos_coin_AptosCoin'(x)
}
function $IsValid'$1_coin_Ghost$aggregate_supply'$1_aptos_coin_AptosCoin''(s: $1_coin_Ghost$aggregate_supply'$1_aptos_coin_AptosCoin'): bool {
    $IsValid'num'($v#$1_coin_Ghost$aggregate_supply'$1_aptos_coin_AptosCoin'(s))
}
function {:inline} $IsEqual'$1_coin_Ghost$aggregate_supply'$1_aptos_coin_AptosCoin''(s1: $1_coin_Ghost$aggregate_supply'$1_aptos_coin_AptosCoin', s2: $1_coin_Ghost$aggregate_supply'$1_aptos_coin_AptosCoin'): bool {
    s1 == s2
}
var $1_coin_Ghost$aggregate_supply'$1_aptos_coin_AptosCoin'_$memory: $Memory $1_coin_Ghost$aggregate_supply'$1_aptos_coin_AptosCoin';

// fun coin::value<aptos_coin::AptosCoin> [baseline] at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.move:566:5+81
procedure {:inline 1} $1_coin_value'$1_aptos_coin_AptosCoin'(_$t0: $1_coin_Coin'$1_aptos_coin_AptosCoin') returns ($ret0: int)
{
    // declare local variables
    var $t1: $1_option_Option'$1_optional_aggregator_OptionalAggregator';
    var $t2: int;
    var $t0: $1_coin_Coin'$1_aptos_coin_AptosCoin';
    var $temp_0'$1_coin_Coin'$1_aptos_coin_AptosCoin'': $1_coin_Coin'$1_aptos_coin_AptosCoin';
    var $temp_0'u64': int;
    $t0 := _$t0;

    // bytecode translation starts here
    // assume Identical($t1, select coin::CoinInfo.supply(global<coin::CoinInfo<#0>>(select type_info::TypeInfo.account_address(type_info::$type_of<#0>())))) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.spec.move:32:9+99
    assume {:print "$at(95,1664,1763)"} true;
    assume ($t1 == $supply#$1_coin_CoinInfo'$1_aptos_coin_AptosCoin'($ResourceValue($1_coin_CoinInfo'$1_aptos_coin_AptosCoin'_$memory, $account_address#$1_type_info_TypeInfo($1_type_info_TypeInfo(1, Vec(DefaultVecMap()[0 := 97][1 := 112][2 := 116][3 := 111][4 := 115][5 := 95][6 := 99][7 := 111][8 := 105][9 := 110], 10), Vec(DefaultVecMap()[0 := 65][1 := 112][2 := 116][3 := 111][4 := 115][5 := 67][6 := 111][7 := 105][8 := 110], 9))))));

    // trace_local[coin]($t0) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.move:566:5+1
    assume {:print "$at(94,21587,21588)"} true;
    assume {:print "$track_local(23,34,0):", $t0} $t0 == $t0;

    // $t2 := get_field<coin::Coin<#0>>.value($t0) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.move:567:9+10
    assume {:print "$at(94,21652,21662)"} true;
    $t2 := $value#$1_coin_Coin'$1_aptos_coin_AptosCoin'($t0);

    // trace_return[0]($t2) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.move:567:9+10
    assume {:print "$track_return(23,34,0):", $t2} $t2 == $t2;

    // label L1 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.move:568:5+1
    assume {:print "$at(94,21667,21668)"} true;
L1:

    // return $t2 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.move:568:5+1
    assume {:print "$at(94,21667,21668)"} true;
    $ret0 := $t2;
    return;

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

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/stake.spec.move:17:10+500
function {:inline} $1_stake_validator_set_is_valid($1_stake_StakePool_$memory: $Memory $1_stake_StakePool, $1_stake_ValidatorConfig_$memory: $Memory $1_stake_ValidatorConfig, $1_stake_ValidatorPerformance_$memory: $Memory $1_stake_ValidatorPerformance, $1_stake_ValidatorSet_$memory: $Memory $1_stake_ValidatorSet): bool {
    (var validator_set := $ResourceValue($1_stake_ValidatorSet_$memory, 1); (((($1_stake_spec_validators_are_initialized($1_stake_StakePool_$memory, $1_stake_ValidatorConfig_$memory, $active_validators#$1_stake_ValidatorSet(validator_set)) && $1_stake_spec_validators_are_initialized($1_stake_StakePool_$memory, $1_stake_ValidatorConfig_$memory, $pending_inactive#$1_stake_ValidatorSet(validator_set))) && $1_stake_spec_validators_are_initialized($1_stake_StakePool_$memory, $1_stake_ValidatorConfig_$memory, $pending_active#$1_stake_ValidatorSet(validator_set))) && $1_stake_spec_validator_indices_are_valid($1_stake_ValidatorConfig_$memory, $1_stake_ValidatorPerformance_$memory, $active_validators#$1_stake_ValidatorSet(validator_set))) && $1_stake_spec_validator_indices_are_valid($1_stake_ValidatorConfig_$memory, $1_stake_ValidatorPerformance_$memory, $pending_inactive#$1_stake_ValidatorSet(validator_set))))
}

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/stake.spec.move:334:10+241
function {:inline} $1_stake_spec_validators_are_initialized($1_stake_StakePool_$memory: $Memory $1_stake_StakePool, $1_stake_ValidatorConfig_$memory: $Memory $1_stake_ValidatorConfig, validators: Vec ($1_stake_ValidatorInfo)): bool {
    (var $range_0 := $Range(0, LenVec(validators)); (forall $i_1: int :: $InRange($range_0, $i_1) ==> (var i := $i_1;
    (($1_stake_spec_has_stake_pool($1_stake_StakePool_$memory, $addr#$1_stake_ValidatorInfo(ReadVec(validators, i))) && $1_stake_spec_has_validator_config($1_stake_ValidatorConfig_$memory, $addr#$1_stake_ValidatorInfo(ReadVec(validators, i))))))))
}

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/stake.spec.move:341:10+234
function {:inline} $1_stake_spec_validator_indices_are_valid($1_stake_ValidatorConfig_$memory: $Memory $1_stake_ValidatorConfig, $1_stake_ValidatorPerformance_$memory: $Memory $1_stake_ValidatorPerformance, validators: Vec ($1_stake_ValidatorInfo)): bool {
    (var $range_2 := $Range(0, LenVec(validators)); (forall $i_3: int :: $InRange($range_2, $i_3) ==> (var i := $i_3;
    (($validator_index#$1_stake_ValidatorConfig($ResourceValue($1_stake_ValidatorConfig_$memory, $addr#$1_stake_ValidatorInfo(ReadVec(validators, i)))) < $1_stake_spec_validator_index_upper_bound($1_stake_ValidatorPerformance_$memory))))))
}

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/stake.spec.move:347:10+122
function {:inline} $1_stake_spec_validator_index_upper_bound($1_stake_ValidatorPerformance_$memory: $Memory $1_stake_ValidatorPerformance): int {
    LenVec($validators#$1_stake_ValidatorPerformance($ResourceValue($1_stake_ValidatorPerformance_$memory, 1)))
}

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/stake.spec.move:351:10+78
function {:inline} $1_stake_spec_has_stake_pool($1_stake_StakePool_$memory: $Memory $1_stake_StakePool, a: int): bool {
    $ResourceExists($1_stake_StakePool_$memory, a)
}

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/stake.spec.move:355:10+90
function {:inline} $1_stake_spec_has_validator_config($1_stake_ValidatorConfig_$memory: $Memory $1_stake_ValidatorConfig, a: int): bool {
    $ResourceExists($1_stake_ValidatorConfig_$memory, a)
}

// struct stake::AddStakeEvent at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/stake.move:210:5+102
type {:datatype} $1_stake_AddStakeEvent;
function {:constructor} $1_stake_AddStakeEvent($pool_address: int, $amount_added: int): $1_stake_AddStakeEvent;
function {:inline} $Update'$1_stake_AddStakeEvent'_pool_address(s: $1_stake_AddStakeEvent, x: int): $1_stake_AddStakeEvent {
    $1_stake_AddStakeEvent(x, $amount_added#$1_stake_AddStakeEvent(s))
}
function {:inline} $Update'$1_stake_AddStakeEvent'_amount_added(s: $1_stake_AddStakeEvent, x: int): $1_stake_AddStakeEvent {
    $1_stake_AddStakeEvent($pool_address#$1_stake_AddStakeEvent(s), x)
}
function $IsValid'$1_stake_AddStakeEvent'(s: $1_stake_AddStakeEvent): bool {
    $IsValid'address'($pool_address#$1_stake_AddStakeEvent(s))
      && $IsValid'u64'($amount_added#$1_stake_AddStakeEvent(s))
}
function {:inline} $IsEqual'$1_stake_AddStakeEvent'(s1: $1_stake_AddStakeEvent, s2: $1_stake_AddStakeEvent): bool {
    s1 == s2
}

// struct stake::DistributeRewardsEvent at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/stake.move:244:5+113
type {:datatype} $1_stake_DistributeRewardsEvent;
function {:constructor} $1_stake_DistributeRewardsEvent($pool_address: int, $rewards_amount: int): $1_stake_DistributeRewardsEvent;
function {:inline} $Update'$1_stake_DistributeRewardsEvent'_pool_address(s: $1_stake_DistributeRewardsEvent, x: int): $1_stake_DistributeRewardsEvent {
    $1_stake_DistributeRewardsEvent(x, $rewards_amount#$1_stake_DistributeRewardsEvent(s))
}
function {:inline} $Update'$1_stake_DistributeRewardsEvent'_rewards_amount(s: $1_stake_DistributeRewardsEvent, x: int): $1_stake_DistributeRewardsEvent {
    $1_stake_DistributeRewardsEvent($pool_address#$1_stake_DistributeRewardsEvent(s), x)
}
function $IsValid'$1_stake_DistributeRewardsEvent'(s: $1_stake_DistributeRewardsEvent): bool {
    $IsValid'address'($pool_address#$1_stake_DistributeRewardsEvent(s))
      && $IsValid'u64'($rewards_amount#$1_stake_DistributeRewardsEvent(s))
}
function {:inline} $IsEqual'$1_stake_DistributeRewardsEvent'(s1: $1_stake_DistributeRewardsEvent, s2: $1_stake_DistributeRewardsEvent): bool {
    s1 == s2
}

// struct stake::IncreaseLockupEvent at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/stake.move:234:5+153
type {:datatype} $1_stake_IncreaseLockupEvent;
function {:constructor} $1_stake_IncreaseLockupEvent($pool_address: int, $old_locked_until_secs: int, $new_locked_until_secs: int): $1_stake_IncreaseLockupEvent;
function {:inline} $Update'$1_stake_IncreaseLockupEvent'_pool_address(s: $1_stake_IncreaseLockupEvent, x: int): $1_stake_IncreaseLockupEvent {
    $1_stake_IncreaseLockupEvent(x, $old_locked_until_secs#$1_stake_IncreaseLockupEvent(s), $new_locked_until_secs#$1_stake_IncreaseLockupEvent(s))
}
function {:inline} $Update'$1_stake_IncreaseLockupEvent'_old_locked_until_secs(s: $1_stake_IncreaseLockupEvent, x: int): $1_stake_IncreaseLockupEvent {
    $1_stake_IncreaseLockupEvent($pool_address#$1_stake_IncreaseLockupEvent(s), x, $new_locked_until_secs#$1_stake_IncreaseLockupEvent(s))
}
function {:inline} $Update'$1_stake_IncreaseLockupEvent'_new_locked_until_secs(s: $1_stake_IncreaseLockupEvent, x: int): $1_stake_IncreaseLockupEvent {
    $1_stake_IncreaseLockupEvent($pool_address#$1_stake_IncreaseLockupEvent(s), $old_locked_until_secs#$1_stake_IncreaseLockupEvent(s), x)
}
function $IsValid'$1_stake_IncreaseLockupEvent'(s: $1_stake_IncreaseLockupEvent): bool {
    $IsValid'address'($pool_address#$1_stake_IncreaseLockupEvent(s))
      && $IsValid'u64'($old_locked_until_secs#$1_stake_IncreaseLockupEvent(s))
      && $IsValid'u64'($new_locked_until_secs#$1_stake_IncreaseLockupEvent(s))
}
function {:inline} $IsEqual'$1_stake_IncreaseLockupEvent'(s1: $1_stake_IncreaseLockupEvent, s2: $1_stake_IncreaseLockupEvent): bool {
    s1 == s2
}

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

// struct stake::JoinValidatorSetEvent at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/stake.move:240:5+83
type {:datatype} $1_stake_JoinValidatorSetEvent;
function {:constructor} $1_stake_JoinValidatorSetEvent($pool_address: int): $1_stake_JoinValidatorSetEvent;
function {:inline} $Update'$1_stake_JoinValidatorSetEvent'_pool_address(s: $1_stake_JoinValidatorSetEvent, x: int): $1_stake_JoinValidatorSetEvent {
    $1_stake_JoinValidatorSetEvent(x)
}
function $IsValid'$1_stake_JoinValidatorSetEvent'(s: $1_stake_JoinValidatorSetEvent): bool {
    $IsValid'address'($pool_address#$1_stake_JoinValidatorSetEvent(s))
}
function {:inline} $IsEqual'$1_stake_JoinValidatorSetEvent'(s1: $1_stake_JoinValidatorSetEvent, s2: $1_stake_JoinValidatorSetEvent): bool {
    s1 == s2
}

// struct stake::LeaveValidatorSetEvent at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/stake.move:259:5+84
type {:datatype} $1_stake_LeaveValidatorSetEvent;
function {:constructor} $1_stake_LeaveValidatorSetEvent($pool_address: int): $1_stake_LeaveValidatorSetEvent;
function {:inline} $Update'$1_stake_LeaveValidatorSetEvent'_pool_address(s: $1_stake_LeaveValidatorSetEvent, x: int): $1_stake_LeaveValidatorSetEvent {
    $1_stake_LeaveValidatorSetEvent(x)
}
function $IsValid'$1_stake_LeaveValidatorSetEvent'(s: $1_stake_LeaveValidatorSetEvent): bool {
    $IsValid'address'($pool_address#$1_stake_LeaveValidatorSetEvent(s))
}
function {:inline} $IsEqual'$1_stake_LeaveValidatorSetEvent'(s1: $1_stake_LeaveValidatorSetEvent, s2: $1_stake_LeaveValidatorSetEvent): bool {
    s1 == s2
}

// struct stake::OwnerCapability at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/stake.move:100:5+76
type {:datatype} $1_stake_OwnerCapability;
function {:constructor} $1_stake_OwnerCapability($pool_address: int): $1_stake_OwnerCapability;
function {:inline} $Update'$1_stake_OwnerCapability'_pool_address(s: $1_stake_OwnerCapability, x: int): $1_stake_OwnerCapability {
    $1_stake_OwnerCapability(x)
}
function $IsValid'$1_stake_OwnerCapability'(s: $1_stake_OwnerCapability): bool {
    $IsValid'address'($pool_address#$1_stake_OwnerCapability(s))
}
function {:inline} $IsEqual'$1_stake_OwnerCapability'(s1: $1_stake_OwnerCapability, s2: $1_stake_OwnerCapability): bool {
    s1 == s2
}
var $1_stake_OwnerCapability_$memory: $Memory $1_stake_OwnerCapability;

// struct stake::ReactivateStakeEvent at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/stake.move:215:5+103
type {:datatype} $1_stake_ReactivateStakeEvent;
function {:constructor} $1_stake_ReactivateStakeEvent($pool_address: int, $amount: int): $1_stake_ReactivateStakeEvent;
function {:inline} $Update'$1_stake_ReactivateStakeEvent'_pool_address(s: $1_stake_ReactivateStakeEvent, x: int): $1_stake_ReactivateStakeEvent {
    $1_stake_ReactivateStakeEvent(x, $amount#$1_stake_ReactivateStakeEvent(s))
}
function {:inline} $Update'$1_stake_ReactivateStakeEvent'_amount(s: $1_stake_ReactivateStakeEvent, x: int): $1_stake_ReactivateStakeEvent {
    $1_stake_ReactivateStakeEvent($pool_address#$1_stake_ReactivateStakeEvent(s), x)
}
function $IsValid'$1_stake_ReactivateStakeEvent'(s: $1_stake_ReactivateStakeEvent): bool {
    $IsValid'address'($pool_address#$1_stake_ReactivateStakeEvent(s))
      && $IsValid'u64'($amount#$1_stake_ReactivateStakeEvent(s))
}
function {:inline} $IsEqual'$1_stake_ReactivateStakeEvent'(s1: $1_stake_ReactivateStakeEvent, s2: $1_stake_ReactivateStakeEvent): bool {
    s1 == s2
}

// struct stake::RegisterValidatorCandidateEvent at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/stake.move:200:5+93
type {:datatype} $1_stake_RegisterValidatorCandidateEvent;
function {:constructor} $1_stake_RegisterValidatorCandidateEvent($pool_address: int): $1_stake_RegisterValidatorCandidateEvent;
function {:inline} $Update'$1_stake_RegisterValidatorCandidateEvent'_pool_address(s: $1_stake_RegisterValidatorCandidateEvent, x: int): $1_stake_RegisterValidatorCandidateEvent {
    $1_stake_RegisterValidatorCandidateEvent(x)
}
function $IsValid'$1_stake_RegisterValidatorCandidateEvent'(s: $1_stake_RegisterValidatorCandidateEvent): bool {
    $IsValid'address'($pool_address#$1_stake_RegisterValidatorCandidateEvent(s))
}
function {:inline} $IsEqual'$1_stake_RegisterValidatorCandidateEvent'(s1: $1_stake_RegisterValidatorCandidateEvent, s2: $1_stake_RegisterValidatorCandidateEvent): bool {
    s1 == s2
}

// struct stake::RotateConsensusKeyEvent at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/stake.move:220:5+169
type {:datatype} $1_stake_RotateConsensusKeyEvent;
function {:constructor} $1_stake_RotateConsensusKeyEvent($pool_address: int, $old_consensus_pubkey: Vec (int), $new_consensus_pubkey: Vec (int)): $1_stake_RotateConsensusKeyEvent;
function {:inline} $Update'$1_stake_RotateConsensusKeyEvent'_pool_address(s: $1_stake_RotateConsensusKeyEvent, x: int): $1_stake_RotateConsensusKeyEvent {
    $1_stake_RotateConsensusKeyEvent(x, $old_consensus_pubkey#$1_stake_RotateConsensusKeyEvent(s), $new_consensus_pubkey#$1_stake_RotateConsensusKeyEvent(s))
}
function {:inline} $Update'$1_stake_RotateConsensusKeyEvent'_old_consensus_pubkey(s: $1_stake_RotateConsensusKeyEvent, x: Vec (int)): $1_stake_RotateConsensusKeyEvent {
    $1_stake_RotateConsensusKeyEvent($pool_address#$1_stake_RotateConsensusKeyEvent(s), x, $new_consensus_pubkey#$1_stake_RotateConsensusKeyEvent(s))
}
function {:inline} $Update'$1_stake_RotateConsensusKeyEvent'_new_consensus_pubkey(s: $1_stake_RotateConsensusKeyEvent, x: Vec (int)): $1_stake_RotateConsensusKeyEvent {
    $1_stake_RotateConsensusKeyEvent($pool_address#$1_stake_RotateConsensusKeyEvent(s), $old_consensus_pubkey#$1_stake_RotateConsensusKeyEvent(s), x)
}
function $IsValid'$1_stake_RotateConsensusKeyEvent'(s: $1_stake_RotateConsensusKeyEvent): bool {
    $IsValid'address'($pool_address#$1_stake_RotateConsensusKeyEvent(s))
      && $IsValid'vec'u8''($old_consensus_pubkey#$1_stake_RotateConsensusKeyEvent(s))
      && $IsValid'vec'u8''($new_consensus_pubkey#$1_stake_RotateConsensusKeyEvent(s))
}
function {:inline} $IsEqual'$1_stake_RotateConsensusKeyEvent'(s1: $1_stake_RotateConsensusKeyEvent, s2: $1_stake_RotateConsensusKeyEvent): bool {
    $IsEqual'address'($pool_address#$1_stake_RotateConsensusKeyEvent(s1), $pool_address#$1_stake_RotateConsensusKeyEvent(s2))
    && $IsEqual'vec'u8''($old_consensus_pubkey#$1_stake_RotateConsensusKeyEvent(s1), $old_consensus_pubkey#$1_stake_RotateConsensusKeyEvent(s2))
    && $IsEqual'vec'u8''($new_consensus_pubkey#$1_stake_RotateConsensusKeyEvent(s1), $new_consensus_pubkey#$1_stake_RotateConsensusKeyEvent(s2))}

// struct stake::SetOperatorEvent at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/stake.move:204:5+140
type {:datatype} $1_stake_SetOperatorEvent;
function {:constructor} $1_stake_SetOperatorEvent($pool_address: int, $old_operator: int, $new_operator: int): $1_stake_SetOperatorEvent;
function {:inline} $Update'$1_stake_SetOperatorEvent'_pool_address(s: $1_stake_SetOperatorEvent, x: int): $1_stake_SetOperatorEvent {
    $1_stake_SetOperatorEvent(x, $old_operator#$1_stake_SetOperatorEvent(s), $new_operator#$1_stake_SetOperatorEvent(s))
}
function {:inline} $Update'$1_stake_SetOperatorEvent'_old_operator(s: $1_stake_SetOperatorEvent, x: int): $1_stake_SetOperatorEvent {
    $1_stake_SetOperatorEvent($pool_address#$1_stake_SetOperatorEvent(s), x, $new_operator#$1_stake_SetOperatorEvent(s))
}
function {:inline} $Update'$1_stake_SetOperatorEvent'_new_operator(s: $1_stake_SetOperatorEvent, x: int): $1_stake_SetOperatorEvent {
    $1_stake_SetOperatorEvent($pool_address#$1_stake_SetOperatorEvent(s), $old_operator#$1_stake_SetOperatorEvent(s), x)
}
function $IsValid'$1_stake_SetOperatorEvent'(s: $1_stake_SetOperatorEvent): bool {
    $IsValid'address'($pool_address#$1_stake_SetOperatorEvent(s))
      && $IsValid'address'($old_operator#$1_stake_SetOperatorEvent(s))
      && $IsValid'address'($new_operator#$1_stake_SetOperatorEvent(s))
}
function {:inline} $IsEqual'$1_stake_SetOperatorEvent'(s1: $1_stake_SetOperatorEvent, s2: $1_stake_SetOperatorEvent): bool {
    s1 == s2
}

// struct stake::StakePool at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/stake.move:115:5+1829
type {:datatype} $1_stake_StakePool;
function {:constructor} $1_stake_StakePool($active: $1_coin_Coin'$1_aptos_coin_AptosCoin', $inactive: $1_coin_Coin'$1_aptos_coin_AptosCoin', $pending_active: $1_coin_Coin'$1_aptos_coin_AptosCoin', $pending_inactive: $1_coin_Coin'$1_aptos_coin_AptosCoin', $locked_until_secs: int, $operator_address: int, $delegated_voter: int, $initialize_validator_events: $1_event_EventHandle'$1_stake_RegisterValidatorCandidateEvent', $set_operator_events: $1_event_EventHandle'$1_stake_SetOperatorEvent', $add_stake_events: $1_event_EventHandle'$1_stake_AddStakeEvent', $reactivate_stake_events: $1_event_EventHandle'$1_stake_ReactivateStakeEvent', $rotate_consensus_key_events: $1_event_EventHandle'$1_stake_RotateConsensusKeyEvent', $update_network_and_fullnode_addresses_events: $1_event_EventHandle'$1_stake_UpdateNetworkAndFullnodeAddressesEvent', $increase_lockup_events: $1_event_EventHandle'$1_stake_IncreaseLockupEvent', $join_validator_set_events: $1_event_EventHandle'$1_stake_JoinValidatorSetEvent', $distribute_rewards_events: $1_event_EventHandle'$1_stake_DistributeRewardsEvent', $unlock_stake_events: $1_event_EventHandle'$1_stake_UnlockStakeEvent', $withdraw_stake_events: $1_event_EventHandle'$1_stake_WithdrawStakeEvent', $leave_validator_set_events: $1_event_EventHandle'$1_stake_LeaveValidatorSetEvent'): $1_stake_StakePool;
function {:inline} $Update'$1_stake_StakePool'_active(s: $1_stake_StakePool, x: $1_coin_Coin'$1_aptos_coin_AptosCoin'): $1_stake_StakePool {
    $1_stake_StakePool(x, $inactive#$1_stake_StakePool(s), $pending_active#$1_stake_StakePool(s), $pending_inactive#$1_stake_StakePool(s), $locked_until_secs#$1_stake_StakePool(s), $operator_address#$1_stake_StakePool(s), $delegated_voter#$1_stake_StakePool(s), $initialize_validator_events#$1_stake_StakePool(s), $set_operator_events#$1_stake_StakePool(s), $add_stake_events#$1_stake_StakePool(s), $reactivate_stake_events#$1_stake_StakePool(s), $rotate_consensus_key_events#$1_stake_StakePool(s), $update_network_and_fullnode_addresses_events#$1_stake_StakePool(s), $increase_lockup_events#$1_stake_StakePool(s), $join_validator_set_events#$1_stake_StakePool(s), $distribute_rewards_events#$1_stake_StakePool(s), $unlock_stake_events#$1_stake_StakePool(s), $withdraw_stake_events#$1_stake_StakePool(s), $leave_validator_set_events#$1_stake_StakePool(s))
}
function {:inline} $Update'$1_stake_StakePool'_inactive(s: $1_stake_StakePool, x: $1_coin_Coin'$1_aptos_coin_AptosCoin'): $1_stake_StakePool {
    $1_stake_StakePool($active#$1_stake_StakePool(s), x, $pending_active#$1_stake_StakePool(s), $pending_inactive#$1_stake_StakePool(s), $locked_until_secs#$1_stake_StakePool(s), $operator_address#$1_stake_StakePool(s), $delegated_voter#$1_stake_StakePool(s), $initialize_validator_events#$1_stake_StakePool(s), $set_operator_events#$1_stake_StakePool(s), $add_stake_events#$1_stake_StakePool(s), $reactivate_stake_events#$1_stake_StakePool(s), $rotate_consensus_key_events#$1_stake_StakePool(s), $update_network_and_fullnode_addresses_events#$1_stake_StakePool(s), $increase_lockup_events#$1_stake_StakePool(s), $join_validator_set_events#$1_stake_StakePool(s), $distribute_rewards_events#$1_stake_StakePool(s), $unlock_stake_events#$1_stake_StakePool(s), $withdraw_stake_events#$1_stake_StakePool(s), $leave_validator_set_events#$1_stake_StakePool(s))
}
function {:inline} $Update'$1_stake_StakePool'_pending_active(s: $1_stake_StakePool, x: $1_coin_Coin'$1_aptos_coin_AptosCoin'): $1_stake_StakePool {
    $1_stake_StakePool($active#$1_stake_StakePool(s), $inactive#$1_stake_StakePool(s), x, $pending_inactive#$1_stake_StakePool(s), $locked_until_secs#$1_stake_StakePool(s), $operator_address#$1_stake_StakePool(s), $delegated_voter#$1_stake_StakePool(s), $initialize_validator_events#$1_stake_StakePool(s), $set_operator_events#$1_stake_StakePool(s), $add_stake_events#$1_stake_StakePool(s), $reactivate_stake_events#$1_stake_StakePool(s), $rotate_consensus_key_events#$1_stake_StakePool(s), $update_network_and_fullnode_addresses_events#$1_stake_StakePool(s), $increase_lockup_events#$1_stake_StakePool(s), $join_validator_set_events#$1_stake_StakePool(s), $distribute_rewards_events#$1_stake_StakePool(s), $unlock_stake_events#$1_stake_StakePool(s), $withdraw_stake_events#$1_stake_StakePool(s), $leave_validator_set_events#$1_stake_StakePool(s))
}
function {:inline} $Update'$1_stake_StakePool'_pending_inactive(s: $1_stake_StakePool, x: $1_coin_Coin'$1_aptos_coin_AptosCoin'): $1_stake_StakePool {
    $1_stake_StakePool($active#$1_stake_StakePool(s), $inactive#$1_stake_StakePool(s), $pending_active#$1_stake_StakePool(s), x, $locked_until_secs#$1_stake_StakePool(s), $operator_address#$1_stake_StakePool(s), $delegated_voter#$1_stake_StakePool(s), $initialize_validator_events#$1_stake_StakePool(s), $set_operator_events#$1_stake_StakePool(s), $add_stake_events#$1_stake_StakePool(s), $reactivate_stake_events#$1_stake_StakePool(s), $rotate_consensus_key_events#$1_stake_StakePool(s), $update_network_and_fullnode_addresses_events#$1_stake_StakePool(s), $increase_lockup_events#$1_stake_StakePool(s), $join_validator_set_events#$1_stake_StakePool(s), $distribute_rewards_events#$1_stake_StakePool(s), $unlock_stake_events#$1_stake_StakePool(s), $withdraw_stake_events#$1_stake_StakePool(s), $leave_validator_set_events#$1_stake_StakePool(s))
}
function {:inline} $Update'$1_stake_StakePool'_locked_until_secs(s: $1_stake_StakePool, x: int): $1_stake_StakePool {
    $1_stake_StakePool($active#$1_stake_StakePool(s), $inactive#$1_stake_StakePool(s), $pending_active#$1_stake_StakePool(s), $pending_inactive#$1_stake_StakePool(s), x, $operator_address#$1_stake_StakePool(s), $delegated_voter#$1_stake_StakePool(s), $initialize_validator_events#$1_stake_StakePool(s), $set_operator_events#$1_stake_StakePool(s), $add_stake_events#$1_stake_StakePool(s), $reactivate_stake_events#$1_stake_StakePool(s), $rotate_consensus_key_events#$1_stake_StakePool(s), $update_network_and_fullnode_addresses_events#$1_stake_StakePool(s), $increase_lockup_events#$1_stake_StakePool(s), $join_validator_set_events#$1_stake_StakePool(s), $distribute_rewards_events#$1_stake_StakePool(s), $unlock_stake_events#$1_stake_StakePool(s), $withdraw_stake_events#$1_stake_StakePool(s), $leave_validator_set_events#$1_stake_StakePool(s))
}
function {:inline} $Update'$1_stake_StakePool'_operator_address(s: $1_stake_StakePool, x: int): $1_stake_StakePool {
    $1_stake_StakePool($active#$1_stake_StakePool(s), $inactive#$1_stake_StakePool(s), $pending_active#$1_stake_StakePool(s), $pending_inactive#$1_stake_StakePool(s), $locked_until_secs#$1_stake_StakePool(s), x, $delegated_voter#$1_stake_StakePool(s), $initialize_validator_events#$1_stake_StakePool(s), $set_operator_events#$1_stake_StakePool(s), $add_stake_events#$1_stake_StakePool(s), $reactivate_stake_events#$1_stake_StakePool(s), $rotate_consensus_key_events#$1_stake_StakePool(s), $update_network_and_fullnode_addresses_events#$1_stake_StakePool(s), $increase_lockup_events#$1_stake_StakePool(s), $join_validator_set_events#$1_stake_StakePool(s), $distribute_rewards_events#$1_stake_StakePool(s), $unlock_stake_events#$1_stake_StakePool(s), $withdraw_stake_events#$1_stake_StakePool(s), $leave_validator_set_events#$1_stake_StakePool(s))
}
function {:inline} $Update'$1_stake_StakePool'_delegated_voter(s: $1_stake_StakePool, x: int): $1_stake_StakePool {
    $1_stake_StakePool($active#$1_stake_StakePool(s), $inactive#$1_stake_StakePool(s), $pending_active#$1_stake_StakePool(s), $pending_inactive#$1_stake_StakePool(s), $locked_until_secs#$1_stake_StakePool(s), $operator_address#$1_stake_StakePool(s), x, $initialize_validator_events#$1_stake_StakePool(s), $set_operator_events#$1_stake_StakePool(s), $add_stake_events#$1_stake_StakePool(s), $reactivate_stake_events#$1_stake_StakePool(s), $rotate_consensus_key_events#$1_stake_StakePool(s), $update_network_and_fullnode_addresses_events#$1_stake_StakePool(s), $increase_lockup_events#$1_stake_StakePool(s), $join_validator_set_events#$1_stake_StakePool(s), $distribute_rewards_events#$1_stake_StakePool(s), $unlock_stake_events#$1_stake_StakePool(s), $withdraw_stake_events#$1_stake_StakePool(s), $leave_validator_set_events#$1_stake_StakePool(s))
}
function {:inline} $Update'$1_stake_StakePool'_initialize_validator_events(s: $1_stake_StakePool, x: $1_event_EventHandle'$1_stake_RegisterValidatorCandidateEvent'): $1_stake_StakePool {
    $1_stake_StakePool($active#$1_stake_StakePool(s), $inactive#$1_stake_StakePool(s), $pending_active#$1_stake_StakePool(s), $pending_inactive#$1_stake_StakePool(s), $locked_until_secs#$1_stake_StakePool(s), $operator_address#$1_stake_StakePool(s), $delegated_voter#$1_stake_StakePool(s), x, $set_operator_events#$1_stake_StakePool(s), $add_stake_events#$1_stake_StakePool(s), $reactivate_stake_events#$1_stake_StakePool(s), $rotate_consensus_key_events#$1_stake_StakePool(s), $update_network_and_fullnode_addresses_events#$1_stake_StakePool(s), $increase_lockup_events#$1_stake_StakePool(s), $join_validator_set_events#$1_stake_StakePool(s), $distribute_rewards_events#$1_stake_StakePool(s), $unlock_stake_events#$1_stake_StakePool(s), $withdraw_stake_events#$1_stake_StakePool(s), $leave_validator_set_events#$1_stake_StakePool(s))
}
function {:inline} $Update'$1_stake_StakePool'_set_operator_events(s: $1_stake_StakePool, x: $1_event_EventHandle'$1_stake_SetOperatorEvent'): $1_stake_StakePool {
    $1_stake_StakePool($active#$1_stake_StakePool(s), $inactive#$1_stake_StakePool(s), $pending_active#$1_stake_StakePool(s), $pending_inactive#$1_stake_StakePool(s), $locked_until_secs#$1_stake_StakePool(s), $operator_address#$1_stake_StakePool(s), $delegated_voter#$1_stake_StakePool(s), $initialize_validator_events#$1_stake_StakePool(s), x, $add_stake_events#$1_stake_StakePool(s), $reactivate_stake_events#$1_stake_StakePool(s), $rotate_consensus_key_events#$1_stake_StakePool(s), $update_network_and_fullnode_addresses_events#$1_stake_StakePool(s), $increase_lockup_events#$1_stake_StakePool(s), $join_validator_set_events#$1_stake_StakePool(s), $distribute_rewards_events#$1_stake_StakePool(s), $unlock_stake_events#$1_stake_StakePool(s), $withdraw_stake_events#$1_stake_StakePool(s), $leave_validator_set_events#$1_stake_StakePool(s))
}
function {:inline} $Update'$1_stake_StakePool'_add_stake_events(s: $1_stake_StakePool, x: $1_event_EventHandle'$1_stake_AddStakeEvent'): $1_stake_StakePool {
    $1_stake_StakePool($active#$1_stake_StakePool(s), $inactive#$1_stake_StakePool(s), $pending_active#$1_stake_StakePool(s), $pending_inactive#$1_stake_StakePool(s), $locked_until_secs#$1_stake_StakePool(s), $operator_address#$1_stake_StakePool(s), $delegated_voter#$1_stake_StakePool(s), $initialize_validator_events#$1_stake_StakePool(s), $set_operator_events#$1_stake_StakePool(s), x, $reactivate_stake_events#$1_stake_StakePool(s), $rotate_consensus_key_events#$1_stake_StakePool(s), $update_network_and_fullnode_addresses_events#$1_stake_StakePool(s), $increase_lockup_events#$1_stake_StakePool(s), $join_validator_set_events#$1_stake_StakePool(s), $distribute_rewards_events#$1_stake_StakePool(s), $unlock_stake_events#$1_stake_StakePool(s), $withdraw_stake_events#$1_stake_StakePool(s), $leave_validator_set_events#$1_stake_StakePool(s))
}
function {:inline} $Update'$1_stake_StakePool'_reactivate_stake_events(s: $1_stake_StakePool, x: $1_event_EventHandle'$1_stake_ReactivateStakeEvent'): $1_stake_StakePool {
    $1_stake_StakePool($active#$1_stake_StakePool(s), $inactive#$1_stake_StakePool(s), $pending_active#$1_stake_StakePool(s), $pending_inactive#$1_stake_StakePool(s), $locked_until_secs#$1_stake_StakePool(s), $operator_address#$1_stake_StakePool(s), $delegated_voter#$1_stake_StakePool(s), $initialize_validator_events#$1_stake_StakePool(s), $set_operator_events#$1_stake_StakePool(s), $add_stake_events#$1_stake_StakePool(s), x, $rotate_consensus_key_events#$1_stake_StakePool(s), $update_network_and_fullnode_addresses_events#$1_stake_StakePool(s), $increase_lockup_events#$1_stake_StakePool(s), $join_validator_set_events#$1_stake_StakePool(s), $distribute_rewards_events#$1_stake_StakePool(s), $unlock_stake_events#$1_stake_StakePool(s), $withdraw_stake_events#$1_stake_StakePool(s), $leave_validator_set_events#$1_stake_StakePool(s))
}
function {:inline} $Update'$1_stake_StakePool'_rotate_consensus_key_events(s: $1_stake_StakePool, x: $1_event_EventHandle'$1_stake_RotateConsensusKeyEvent'): $1_stake_StakePool {
    $1_stake_StakePool($active#$1_stake_StakePool(s), $inactive#$1_stake_StakePool(s), $pending_active#$1_stake_StakePool(s), $pending_inactive#$1_stake_StakePool(s), $locked_until_secs#$1_stake_StakePool(s), $operator_address#$1_stake_StakePool(s), $delegated_voter#$1_stake_StakePool(s), $initialize_validator_events#$1_stake_StakePool(s), $set_operator_events#$1_stake_StakePool(s), $add_stake_events#$1_stake_StakePool(s), $reactivate_stake_events#$1_stake_StakePool(s), x, $update_network_and_fullnode_addresses_events#$1_stake_StakePool(s), $increase_lockup_events#$1_stake_StakePool(s), $join_validator_set_events#$1_stake_StakePool(s), $distribute_rewards_events#$1_stake_StakePool(s), $unlock_stake_events#$1_stake_StakePool(s), $withdraw_stake_events#$1_stake_StakePool(s), $leave_validator_set_events#$1_stake_StakePool(s))
}
function {:inline} $Update'$1_stake_StakePool'_update_network_and_fullnode_addresses_events(s: $1_stake_StakePool, x: $1_event_EventHandle'$1_stake_UpdateNetworkAndFullnodeAddressesEvent'): $1_stake_StakePool {
    $1_stake_StakePool($active#$1_stake_StakePool(s), $inactive#$1_stake_StakePool(s), $pending_active#$1_stake_StakePool(s), $pending_inactive#$1_stake_StakePool(s), $locked_until_secs#$1_stake_StakePool(s), $operator_address#$1_stake_StakePool(s), $delegated_voter#$1_stake_StakePool(s), $initialize_validator_events#$1_stake_StakePool(s), $set_operator_events#$1_stake_StakePool(s), $add_stake_events#$1_stake_StakePool(s), $reactivate_stake_events#$1_stake_StakePool(s), $rotate_consensus_key_events#$1_stake_StakePool(s), x, $increase_lockup_events#$1_stake_StakePool(s), $join_validator_set_events#$1_stake_StakePool(s), $distribute_rewards_events#$1_stake_StakePool(s), $unlock_stake_events#$1_stake_StakePool(s), $withdraw_stake_events#$1_stake_StakePool(s), $leave_validator_set_events#$1_stake_StakePool(s))
}
function {:inline} $Update'$1_stake_StakePool'_increase_lockup_events(s: $1_stake_StakePool, x: $1_event_EventHandle'$1_stake_IncreaseLockupEvent'): $1_stake_StakePool {
    $1_stake_StakePool($active#$1_stake_StakePool(s), $inactive#$1_stake_StakePool(s), $pending_active#$1_stake_StakePool(s), $pending_inactive#$1_stake_StakePool(s), $locked_until_secs#$1_stake_StakePool(s), $operator_address#$1_stake_StakePool(s), $delegated_voter#$1_stake_StakePool(s), $initialize_validator_events#$1_stake_StakePool(s), $set_operator_events#$1_stake_StakePool(s), $add_stake_events#$1_stake_StakePool(s), $reactivate_stake_events#$1_stake_StakePool(s), $rotate_consensus_key_events#$1_stake_StakePool(s), $update_network_and_fullnode_addresses_events#$1_stake_StakePool(s), x, $join_validator_set_events#$1_stake_StakePool(s), $distribute_rewards_events#$1_stake_StakePool(s), $unlock_stake_events#$1_stake_StakePool(s), $withdraw_stake_events#$1_stake_StakePool(s), $leave_validator_set_events#$1_stake_StakePool(s))
}
function {:inline} $Update'$1_stake_StakePool'_join_validator_set_events(s: $1_stake_StakePool, x: $1_event_EventHandle'$1_stake_JoinValidatorSetEvent'): $1_stake_StakePool {
    $1_stake_StakePool($active#$1_stake_StakePool(s), $inactive#$1_stake_StakePool(s), $pending_active#$1_stake_StakePool(s), $pending_inactive#$1_stake_StakePool(s), $locked_until_secs#$1_stake_StakePool(s), $operator_address#$1_stake_StakePool(s), $delegated_voter#$1_stake_StakePool(s), $initialize_validator_events#$1_stake_StakePool(s), $set_operator_events#$1_stake_StakePool(s), $add_stake_events#$1_stake_StakePool(s), $reactivate_stake_events#$1_stake_StakePool(s), $rotate_consensus_key_events#$1_stake_StakePool(s), $update_network_and_fullnode_addresses_events#$1_stake_StakePool(s), $increase_lockup_events#$1_stake_StakePool(s), x, $distribute_rewards_events#$1_stake_StakePool(s), $unlock_stake_events#$1_stake_StakePool(s), $withdraw_stake_events#$1_stake_StakePool(s), $leave_validator_set_events#$1_stake_StakePool(s))
}
function {:inline} $Update'$1_stake_StakePool'_distribute_rewards_events(s: $1_stake_StakePool, x: $1_event_EventHandle'$1_stake_DistributeRewardsEvent'): $1_stake_StakePool {
    $1_stake_StakePool($active#$1_stake_StakePool(s), $inactive#$1_stake_StakePool(s), $pending_active#$1_stake_StakePool(s), $pending_inactive#$1_stake_StakePool(s), $locked_until_secs#$1_stake_StakePool(s), $operator_address#$1_stake_StakePool(s), $delegated_voter#$1_stake_StakePool(s), $initialize_validator_events#$1_stake_StakePool(s), $set_operator_events#$1_stake_StakePool(s), $add_stake_events#$1_stake_StakePool(s), $reactivate_stake_events#$1_stake_StakePool(s), $rotate_consensus_key_events#$1_stake_StakePool(s), $update_network_and_fullnode_addresses_events#$1_stake_StakePool(s), $increase_lockup_events#$1_stake_StakePool(s), $join_validator_set_events#$1_stake_StakePool(s), x, $unlock_stake_events#$1_stake_StakePool(s), $withdraw_stake_events#$1_stake_StakePool(s), $leave_validator_set_events#$1_stake_StakePool(s))
}
function {:inline} $Update'$1_stake_StakePool'_unlock_stake_events(s: $1_stake_StakePool, x: $1_event_EventHandle'$1_stake_UnlockStakeEvent'): $1_stake_StakePool {
    $1_stake_StakePool($active#$1_stake_StakePool(s), $inactive#$1_stake_StakePool(s), $pending_active#$1_stake_StakePool(s), $pending_inactive#$1_stake_StakePool(s), $locked_until_secs#$1_stake_StakePool(s), $operator_address#$1_stake_StakePool(s), $delegated_voter#$1_stake_StakePool(s), $initialize_validator_events#$1_stake_StakePool(s), $set_operator_events#$1_stake_StakePool(s), $add_stake_events#$1_stake_StakePool(s), $reactivate_stake_events#$1_stake_StakePool(s), $rotate_consensus_key_events#$1_stake_StakePool(s), $update_network_and_fullnode_addresses_events#$1_stake_StakePool(s), $increase_lockup_events#$1_stake_StakePool(s), $join_validator_set_events#$1_stake_StakePool(s), $distribute_rewards_events#$1_stake_StakePool(s), x, $withdraw_stake_events#$1_stake_StakePool(s), $leave_validator_set_events#$1_stake_StakePool(s))
}
function {:inline} $Update'$1_stake_StakePool'_withdraw_stake_events(s: $1_stake_StakePool, x: $1_event_EventHandle'$1_stake_WithdrawStakeEvent'): $1_stake_StakePool {
    $1_stake_StakePool($active#$1_stake_StakePool(s), $inactive#$1_stake_StakePool(s), $pending_active#$1_stake_StakePool(s), $pending_inactive#$1_stake_StakePool(s), $locked_until_secs#$1_stake_StakePool(s), $operator_address#$1_stake_StakePool(s), $delegated_voter#$1_stake_StakePool(s), $initialize_validator_events#$1_stake_StakePool(s), $set_operator_events#$1_stake_StakePool(s), $add_stake_events#$1_stake_StakePool(s), $reactivate_stake_events#$1_stake_StakePool(s), $rotate_consensus_key_events#$1_stake_StakePool(s), $update_network_and_fullnode_addresses_events#$1_stake_StakePool(s), $increase_lockup_events#$1_stake_StakePool(s), $join_validator_set_events#$1_stake_StakePool(s), $distribute_rewards_events#$1_stake_StakePool(s), $unlock_stake_events#$1_stake_StakePool(s), x, $leave_validator_set_events#$1_stake_StakePool(s))
}
function {:inline} $Update'$1_stake_StakePool'_leave_validator_set_events(s: $1_stake_StakePool, x: $1_event_EventHandle'$1_stake_LeaveValidatorSetEvent'): $1_stake_StakePool {
    $1_stake_StakePool($active#$1_stake_StakePool(s), $inactive#$1_stake_StakePool(s), $pending_active#$1_stake_StakePool(s), $pending_inactive#$1_stake_StakePool(s), $locked_until_secs#$1_stake_StakePool(s), $operator_address#$1_stake_StakePool(s), $delegated_voter#$1_stake_StakePool(s), $initialize_validator_events#$1_stake_StakePool(s), $set_operator_events#$1_stake_StakePool(s), $add_stake_events#$1_stake_StakePool(s), $reactivate_stake_events#$1_stake_StakePool(s), $rotate_consensus_key_events#$1_stake_StakePool(s), $update_network_and_fullnode_addresses_events#$1_stake_StakePool(s), $increase_lockup_events#$1_stake_StakePool(s), $join_validator_set_events#$1_stake_StakePool(s), $distribute_rewards_events#$1_stake_StakePool(s), $unlock_stake_events#$1_stake_StakePool(s), $withdraw_stake_events#$1_stake_StakePool(s), x)
}
function $IsValid'$1_stake_StakePool'(s: $1_stake_StakePool): bool {
    $IsValid'$1_coin_Coin'$1_aptos_coin_AptosCoin''($active#$1_stake_StakePool(s))
      && $IsValid'$1_coin_Coin'$1_aptos_coin_AptosCoin''($inactive#$1_stake_StakePool(s))
      && $IsValid'$1_coin_Coin'$1_aptos_coin_AptosCoin''($pending_active#$1_stake_StakePool(s))
      && $IsValid'$1_coin_Coin'$1_aptos_coin_AptosCoin''($pending_inactive#$1_stake_StakePool(s))
      && $IsValid'u64'($locked_until_secs#$1_stake_StakePool(s))
      && $IsValid'address'($operator_address#$1_stake_StakePool(s))
      && $IsValid'address'($delegated_voter#$1_stake_StakePool(s))
      && $IsValid'$1_event_EventHandle'$1_stake_RegisterValidatorCandidateEvent''($initialize_validator_events#$1_stake_StakePool(s))
      && $IsValid'$1_event_EventHandle'$1_stake_SetOperatorEvent''($set_operator_events#$1_stake_StakePool(s))
      && $IsValid'$1_event_EventHandle'$1_stake_AddStakeEvent''($add_stake_events#$1_stake_StakePool(s))
      && $IsValid'$1_event_EventHandle'$1_stake_ReactivateStakeEvent''($reactivate_stake_events#$1_stake_StakePool(s))
      && $IsValid'$1_event_EventHandle'$1_stake_RotateConsensusKeyEvent''($rotate_consensus_key_events#$1_stake_StakePool(s))
      && $IsValid'$1_event_EventHandle'$1_stake_UpdateNetworkAndFullnodeAddressesEvent''($update_network_and_fullnode_addresses_events#$1_stake_StakePool(s))
      && $IsValid'$1_event_EventHandle'$1_stake_IncreaseLockupEvent''($increase_lockup_events#$1_stake_StakePool(s))
      && $IsValid'$1_event_EventHandle'$1_stake_JoinValidatorSetEvent''($join_validator_set_events#$1_stake_StakePool(s))
      && $IsValid'$1_event_EventHandle'$1_stake_DistributeRewardsEvent''($distribute_rewards_events#$1_stake_StakePool(s))
      && $IsValid'$1_event_EventHandle'$1_stake_UnlockStakeEvent''($unlock_stake_events#$1_stake_StakePool(s))
      && $IsValid'$1_event_EventHandle'$1_stake_WithdrawStakeEvent''($withdraw_stake_events#$1_stake_StakePool(s))
      && $IsValid'$1_event_EventHandle'$1_stake_LeaveValidatorSetEvent''($leave_validator_set_events#$1_stake_StakePool(s))
}
function {:inline} $IsEqual'$1_stake_StakePool'(s1: $1_stake_StakePool, s2: $1_stake_StakePool): bool {
    s1 == s2
}
var $1_stake_StakePool_$memory: $Memory $1_stake_StakePool;

// struct stake::UnlockStakeEvent at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/stake.move:249:5+108
type {:datatype} $1_stake_UnlockStakeEvent;
function {:constructor} $1_stake_UnlockStakeEvent($pool_address: int, $amount_unlocked: int): $1_stake_UnlockStakeEvent;
function {:inline} $Update'$1_stake_UnlockStakeEvent'_pool_address(s: $1_stake_UnlockStakeEvent, x: int): $1_stake_UnlockStakeEvent {
    $1_stake_UnlockStakeEvent(x, $amount_unlocked#$1_stake_UnlockStakeEvent(s))
}
function {:inline} $Update'$1_stake_UnlockStakeEvent'_amount_unlocked(s: $1_stake_UnlockStakeEvent, x: int): $1_stake_UnlockStakeEvent {
    $1_stake_UnlockStakeEvent($pool_address#$1_stake_UnlockStakeEvent(s), x)
}
function $IsValid'$1_stake_UnlockStakeEvent'(s: $1_stake_UnlockStakeEvent): bool {
    $IsValid'address'($pool_address#$1_stake_UnlockStakeEvent(s))
      && $IsValid'u64'($amount_unlocked#$1_stake_UnlockStakeEvent(s))
}
function {:inline} $IsEqual'$1_stake_UnlockStakeEvent'(s1: $1_stake_UnlockStakeEvent, s2: $1_stake_UnlockStakeEvent): bool {
    s1 == s2
}

// struct stake::UpdateNetworkAndFullnodeAddressesEvent at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/stake.move:226:5+274
type {:datatype} $1_stake_UpdateNetworkAndFullnodeAddressesEvent;
function {:constructor} $1_stake_UpdateNetworkAndFullnodeAddressesEvent($pool_address: int, $old_network_addresses: Vec (int), $new_network_addresses: Vec (int), $old_fullnode_addresses: Vec (int), $new_fullnode_addresses: Vec (int)): $1_stake_UpdateNetworkAndFullnodeAddressesEvent;
function {:inline} $Update'$1_stake_UpdateNetworkAndFullnodeAddressesEvent'_pool_address(s: $1_stake_UpdateNetworkAndFullnodeAddressesEvent, x: int): $1_stake_UpdateNetworkAndFullnodeAddressesEvent {
    $1_stake_UpdateNetworkAndFullnodeAddressesEvent(x, $old_network_addresses#$1_stake_UpdateNetworkAndFullnodeAddressesEvent(s), $new_network_addresses#$1_stake_UpdateNetworkAndFullnodeAddressesEvent(s), $old_fullnode_addresses#$1_stake_UpdateNetworkAndFullnodeAddressesEvent(s), $new_fullnode_addresses#$1_stake_UpdateNetworkAndFullnodeAddressesEvent(s))
}
function {:inline} $Update'$1_stake_UpdateNetworkAndFullnodeAddressesEvent'_old_network_addresses(s: $1_stake_UpdateNetworkAndFullnodeAddressesEvent, x: Vec (int)): $1_stake_UpdateNetworkAndFullnodeAddressesEvent {
    $1_stake_UpdateNetworkAndFullnodeAddressesEvent($pool_address#$1_stake_UpdateNetworkAndFullnodeAddressesEvent(s), x, $new_network_addresses#$1_stake_UpdateNetworkAndFullnodeAddressesEvent(s), $old_fullnode_addresses#$1_stake_UpdateNetworkAndFullnodeAddressesEvent(s), $new_fullnode_addresses#$1_stake_UpdateNetworkAndFullnodeAddressesEvent(s))
}
function {:inline} $Update'$1_stake_UpdateNetworkAndFullnodeAddressesEvent'_new_network_addresses(s: $1_stake_UpdateNetworkAndFullnodeAddressesEvent, x: Vec (int)): $1_stake_UpdateNetworkAndFullnodeAddressesEvent {
    $1_stake_UpdateNetworkAndFullnodeAddressesEvent($pool_address#$1_stake_UpdateNetworkAndFullnodeAddressesEvent(s), $old_network_addresses#$1_stake_UpdateNetworkAndFullnodeAddressesEvent(s), x, $old_fullnode_addresses#$1_stake_UpdateNetworkAndFullnodeAddressesEvent(s), $new_fullnode_addresses#$1_stake_UpdateNetworkAndFullnodeAddressesEvent(s))
}
function {:inline} $Update'$1_stake_UpdateNetworkAndFullnodeAddressesEvent'_old_fullnode_addresses(s: $1_stake_UpdateNetworkAndFullnodeAddressesEvent, x: Vec (int)): $1_stake_UpdateNetworkAndFullnodeAddressesEvent {
    $1_stake_UpdateNetworkAndFullnodeAddressesEvent($pool_address#$1_stake_UpdateNetworkAndFullnodeAddressesEvent(s), $old_network_addresses#$1_stake_UpdateNetworkAndFullnodeAddressesEvent(s), $new_network_addresses#$1_stake_UpdateNetworkAndFullnodeAddressesEvent(s), x, $new_fullnode_addresses#$1_stake_UpdateNetworkAndFullnodeAddressesEvent(s))
}
function {:inline} $Update'$1_stake_UpdateNetworkAndFullnodeAddressesEvent'_new_fullnode_addresses(s: $1_stake_UpdateNetworkAndFullnodeAddressesEvent, x: Vec (int)): $1_stake_UpdateNetworkAndFullnodeAddressesEvent {
    $1_stake_UpdateNetworkAndFullnodeAddressesEvent($pool_address#$1_stake_UpdateNetworkAndFullnodeAddressesEvent(s), $old_network_addresses#$1_stake_UpdateNetworkAndFullnodeAddressesEvent(s), $new_network_addresses#$1_stake_UpdateNetworkAndFullnodeAddressesEvent(s), $old_fullnode_addresses#$1_stake_UpdateNetworkAndFullnodeAddressesEvent(s), x)
}
function $IsValid'$1_stake_UpdateNetworkAndFullnodeAddressesEvent'(s: $1_stake_UpdateNetworkAndFullnodeAddressesEvent): bool {
    $IsValid'address'($pool_address#$1_stake_UpdateNetworkAndFullnodeAddressesEvent(s))
      && $IsValid'vec'u8''($old_network_addresses#$1_stake_UpdateNetworkAndFullnodeAddressesEvent(s))
      && $IsValid'vec'u8''($new_network_addresses#$1_stake_UpdateNetworkAndFullnodeAddressesEvent(s))
      && $IsValid'vec'u8''($old_fullnode_addresses#$1_stake_UpdateNetworkAndFullnodeAddressesEvent(s))
      && $IsValid'vec'u8''($new_fullnode_addresses#$1_stake_UpdateNetworkAndFullnodeAddressesEvent(s))
}
function {:inline} $IsEqual'$1_stake_UpdateNetworkAndFullnodeAddressesEvent'(s1: $1_stake_UpdateNetworkAndFullnodeAddressesEvent, s2: $1_stake_UpdateNetworkAndFullnodeAddressesEvent): bool {
    $IsEqual'address'($pool_address#$1_stake_UpdateNetworkAndFullnodeAddressesEvent(s1), $pool_address#$1_stake_UpdateNetworkAndFullnodeAddressesEvent(s2))
    && $IsEqual'vec'u8''($old_network_addresses#$1_stake_UpdateNetworkAndFullnodeAddressesEvent(s1), $old_network_addresses#$1_stake_UpdateNetworkAndFullnodeAddressesEvent(s2))
    && $IsEqual'vec'u8''($new_network_addresses#$1_stake_UpdateNetworkAndFullnodeAddressesEvent(s1), $new_network_addresses#$1_stake_UpdateNetworkAndFullnodeAddressesEvent(s2))
    && $IsEqual'vec'u8''($old_fullnode_addresses#$1_stake_UpdateNetworkAndFullnodeAddressesEvent(s1), $old_fullnode_addresses#$1_stake_UpdateNetworkAndFullnodeAddressesEvent(s2))
    && $IsEqual'vec'u8''($new_fullnode_addresses#$1_stake_UpdateNetworkAndFullnodeAddressesEvent(s1), $new_fullnode_addresses#$1_stake_UpdateNetworkAndFullnodeAddressesEvent(s2))}

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

// struct stake::WithdrawStakeEvent at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/stake.move:254:5+111
type {:datatype} $1_stake_WithdrawStakeEvent;
function {:constructor} $1_stake_WithdrawStakeEvent($pool_address: int, $amount_withdrawn: int): $1_stake_WithdrawStakeEvent;
function {:inline} $Update'$1_stake_WithdrawStakeEvent'_pool_address(s: $1_stake_WithdrawStakeEvent, x: int): $1_stake_WithdrawStakeEvent {
    $1_stake_WithdrawStakeEvent(x, $amount_withdrawn#$1_stake_WithdrawStakeEvent(s))
}
function {:inline} $Update'$1_stake_WithdrawStakeEvent'_amount_withdrawn(s: $1_stake_WithdrawStakeEvent, x: int): $1_stake_WithdrawStakeEvent {
    $1_stake_WithdrawStakeEvent($pool_address#$1_stake_WithdrawStakeEvent(s), x)
}
function $IsValid'$1_stake_WithdrawStakeEvent'(s: $1_stake_WithdrawStakeEvent): bool {
    $IsValid'address'($pool_address#$1_stake_WithdrawStakeEvent(s))
      && $IsValid'u64'($amount_withdrawn#$1_stake_WithdrawStakeEvent(s))
}
function {:inline} $IsEqual'$1_stake_WithdrawStakeEvent'(s1: $1_stake_WithdrawStakeEvent, s2: $1_stake_WithdrawStakeEvent): bool {
    s1 == s2
}

// fun stake::assert_stake_pool_exists [baseline] at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/stake.move:1319:5+162
procedure {:inline 1} $1_stake_assert_stake_pool_exists(_$t0: int) returns ()
{
    // declare local variables
    var $t1: bool;
    var $t2: int;
    var $t3: int;
    var $t4: int;
    var $t0: int;
    var $temp_0'address': int;
    $t0 := _$t0;

    // bytecode translation starts here
    // trace_local[pool_address]($t0) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/stake.move:1319:5+1
    assume {:print "$at(131,62960,62961)"} true;
    assume {:print "$track_local(38,5,0):", $t0} $t0 == $t0;

    // $t1 := stake::stake_pool_exists($t0) on_abort goto L4 with $t2 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/stake.move:1320:17+31
    assume {:print "$at(131,63030,63061)"} true;
    call $t1 := $1_stake_stake_pool_exists($t0);
    if ($abort_flag) {
        assume {:print "$at(131,63030,63061)"} true;
        $t2 := $abort_code;
        assume {:print "$track_abort(38,5):", $t2} $t2 == $t2;
        goto L4;
    }

    // if ($t1) goto L1 else goto L0 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/stake.move:1320:9+93
    if ($t1) { goto L1; } else { goto L0; }

    // label L1 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/stake.move:1320:9+93
L1:

    // goto L2 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/stake.move:1320:9+93
    assume {:print "$at(131,63022,63115)"} true;
    goto L2;

    // label L0 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/stake.move:1320:74+26
L0:

    // $t3 := 14 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/stake.move:1320:74+26
    assume {:print "$at(131,63087,63113)"} true;
    $t3 := 14;
    assume $IsValid'u64'($t3);

    // $t4 := error::invalid_argument($t3) on_abort goto L4 with $t2 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/stake.move:1320:50+51
    call $t4 := $1_error_invalid_argument($t3);
    if ($abort_flag) {
        assume {:print "$at(131,63063,63114)"} true;
        $t2 := $abort_code;
        assume {:print "$track_abort(38,5):", $t2} $t2 == $t2;
        goto L4;
    }

    // trace_abort($t4) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/stake.move:1320:9+93
    assume {:print "$at(131,63022,63115)"} true;
    assume {:print "$track_abort(38,5):", $t4} $t4 == $t4;

    // $t2 := move($t4) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/stake.move:1320:9+93
    $t2 := $t4;

    // goto L4 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/stake.move:1320:9+93
    goto L4;

    // label L2 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/stake.move:1320:102+1
L2:

    // label L3 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/stake.move:1321:5+1
    assume {:print "$at(131,63121,63122)"} true;
L3:

    // return () at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/stake.move:1321:5+1
    assume {:print "$at(131,63121,63122)"} true;
    return;

    // label L4 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/stake.move:1321:5+1
L4:

    // abort($t2) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/stake.move:1321:5+1
    assume {:print "$at(131,63121,63122)"} true;
    $abort_code := $t2;
    $abort_flag := true;
    return;

}

// fun stake::get_stake [baseline] at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/stake.move:315:5+425
procedure {:inline 1} $1_stake_get_stake(_$t0: int) returns ($ret0: int, $ret1: int, $ret2: int, $ret3: int)
{
    // declare local variables
    var $t1: $1_stake_StakePool;
    var $t2: int;
    var $t3: $1_stake_StakePool;
    var $t4: $1_coin_Coin'$1_aptos_coin_AptosCoin';
    var $t5: $1_option_Option'$1_optional_aggregator_OptionalAggregator';
    var $t6: int;
    var $t7: $1_coin_Coin'$1_aptos_coin_AptosCoin';
    var $t8: $1_option_Option'$1_optional_aggregator_OptionalAggregator';
    var $t9: int;
    var $t10: $1_coin_Coin'$1_aptos_coin_AptosCoin';
    var $t11: $1_option_Option'$1_optional_aggregator_OptionalAggregator';
    var $t12: int;
    var $t13: $1_coin_Coin'$1_aptos_coin_AptosCoin';
    var $t14: $1_option_Option'$1_optional_aggregator_OptionalAggregator';
    var $t15: int;
    var $t0: int;
    var $temp_0'$1_stake_StakePool': $1_stake_StakePool;
    var $temp_0'address': int;
    var $temp_0'u64': int;
    $t0 := _$t0;

    // bytecode translation starts here
    // trace_local[pool_address]($t0) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/stake.move:315:5+1
    assume {:print "$at(131,14196,14197)"} true;
    assume {:print "$track_local(38,22,0):", $t0} $t0 == $t0;

    // stake::assert_stake_pool_exists($t0) on_abort goto L2 with $t2 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/stake.move:316:9+38
    assume {:print "$at(131,14291,14329)"} true;
    call $1_stake_assert_stake_pool_exists($t0);
    if ($abort_flag) {
        assume {:print "$at(131,14291,14329)"} true;
        $t2 := $abort_code;
        assume {:print "$track_abort(38,22):", $t2} $t2 == $t2;
        goto L2;
    }

    // $t3 := get_global<stake::StakePool>($t0) on_abort goto L2 with $t2 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/stake.move:317:26+13
    assume {:print "$at(131,14356,14369)"} true;
    if (!$ResourceExists($1_stake_StakePool_$memory, $t0)) {
        call $ExecFailureAbort();
    } else {
        $t3 := $ResourceValue($1_stake_StakePool_$memory, $t0);
    }
    if ($abort_flag) {
        assume {:print "$at(131,14356,14369)"} true;
        $t2 := $abort_code;
        assume {:print "$track_abort(38,22):", $t2} $t2 == $t2;
        goto L2;
    }

    // trace_local[stake_pool]($t3) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/stake.move:317:13+10
    assume {:print "$track_local(38,22,1):", $t3} $t3 == $t3;

    // $t4 := get_field<stake::StakePool>.active($t3) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/stake.move:319:25+18
    assume {:print "$at(131,14430,14448)"} true;
    $t4 := $active#$1_stake_StakePool($t3);

    // assume Identical($t5, select coin::CoinInfo.supply(global<coin::CoinInfo<aptos_coin::AptosCoin>>(select type_info::TypeInfo.account_address(type_info::$type_of<aptos_coin::AptosCoin>())))) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.spec.move:32:9+99
    assume {:print "$at(95,1664,1763)"} true;
    assume ($t5 == $supply#$1_coin_CoinInfo'$1_aptos_coin_AptosCoin'($ResourceValue($1_coin_CoinInfo'$1_aptos_coin_AptosCoin'_$memory, $account_address#$1_type_info_TypeInfo($1_type_info_TypeInfo(1, Vec(DefaultVecMap()[0 := 97][1 := 112][2 := 116][3 := 111][4 := 115][5 := 95][6 := 99][7 := 111][8 := 105][9 := 110], 10), Vec(DefaultVecMap()[0 := 65][1 := 112][2 := 116][3 := 111][4 := 115][5 := 67][6 := 111][7 := 105][8 := 110], 9))))));

    // $t6 := coin::value<aptos_coin::AptosCoin>($t4) on_abort goto L2 with $t2 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/stake.move:319:13+31
    assume {:print "$at(131,14418,14449)"} true;
    call $t6 := $1_coin_value'$1_aptos_coin_AptosCoin'($t4);
    if ($abort_flag) {
        assume {:print "$at(131,14418,14449)"} true;
        $t2 := $abort_code;
        assume {:print "$track_abort(38,22):", $t2} $t2 == $t2;
        goto L2;
    }

    // $t7 := get_field<stake::StakePool>.inactive($t3) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/stake.move:320:25+20
    assume {:print "$at(131,14475,14495)"} true;
    $t7 := $inactive#$1_stake_StakePool($t3);

    // assume Identical($t8, select coin::CoinInfo.supply(global<coin::CoinInfo<aptos_coin::AptosCoin>>(select type_info::TypeInfo.account_address(type_info::$type_of<aptos_coin::AptosCoin>())))) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.spec.move:32:9+99
    assume {:print "$at(95,1664,1763)"} true;
    assume ($t8 == $supply#$1_coin_CoinInfo'$1_aptos_coin_AptosCoin'($ResourceValue($1_coin_CoinInfo'$1_aptos_coin_AptosCoin'_$memory, $account_address#$1_type_info_TypeInfo($1_type_info_TypeInfo(1, Vec(DefaultVecMap()[0 := 97][1 := 112][2 := 116][3 := 111][4 := 115][5 := 95][6 := 99][7 := 111][8 := 105][9 := 110], 10), Vec(DefaultVecMap()[0 := 65][1 := 112][2 := 116][3 := 111][4 := 115][5 := 67][6 := 111][7 := 105][8 := 110], 9))))));

    // $t9 := coin::value<aptos_coin::AptosCoin>($t7) on_abort goto L2 with $t2 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/stake.move:320:13+33
    assume {:print "$at(131,14463,14496)"} true;
    call $t9 := $1_coin_value'$1_aptos_coin_AptosCoin'($t7);
    if ($abort_flag) {
        assume {:print "$at(131,14463,14496)"} true;
        $t2 := $abort_code;
        assume {:print "$track_abort(38,22):", $t2} $t2 == $t2;
        goto L2;
    }

    // $t10 := get_field<stake::StakePool>.pending_active($t3) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/stake.move:321:25+26
    assume {:print "$at(131,14522,14548)"} true;
    $t10 := $pending_active#$1_stake_StakePool($t3);

    // assume Identical($t11, select coin::CoinInfo.supply(global<coin::CoinInfo<aptos_coin::AptosCoin>>(select type_info::TypeInfo.account_address(type_info::$type_of<aptos_coin::AptosCoin>())))) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.spec.move:32:9+99
    assume {:print "$at(95,1664,1763)"} true;
    assume ($t11 == $supply#$1_coin_CoinInfo'$1_aptos_coin_AptosCoin'($ResourceValue($1_coin_CoinInfo'$1_aptos_coin_AptosCoin'_$memory, $account_address#$1_type_info_TypeInfo($1_type_info_TypeInfo(1, Vec(DefaultVecMap()[0 := 97][1 := 112][2 := 116][3 := 111][4 := 115][5 := 95][6 := 99][7 := 111][8 := 105][9 := 110], 10), Vec(DefaultVecMap()[0 := 65][1 := 112][2 := 116][3 := 111][4 := 115][5 := 67][6 := 111][7 := 105][8 := 110], 9))))));

    // $t12 := coin::value<aptos_coin::AptosCoin>($t10) on_abort goto L2 with $t2 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/stake.move:321:13+39
    assume {:print "$at(131,14510,14549)"} true;
    call $t12 := $1_coin_value'$1_aptos_coin_AptosCoin'($t10);
    if ($abort_flag) {
        assume {:print "$at(131,14510,14549)"} true;
        $t2 := $abort_code;
        assume {:print "$track_abort(38,22):", $t2} $t2 == $t2;
        goto L2;
    }

    // $t13 := get_field<stake::StakePool>.pending_inactive($t3) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/stake.move:322:25+28
    assume {:print "$at(131,14575,14603)"} true;
    $t13 := $pending_inactive#$1_stake_StakePool($t3);

    // assume Identical($t14, select coin::CoinInfo.supply(global<coin::CoinInfo<aptos_coin::AptosCoin>>(select type_info::TypeInfo.account_address(type_info::$type_of<aptos_coin::AptosCoin>())))) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.spec.move:32:9+99
    assume {:print "$at(95,1664,1763)"} true;
    assume ($t14 == $supply#$1_coin_CoinInfo'$1_aptos_coin_AptosCoin'($ResourceValue($1_coin_CoinInfo'$1_aptos_coin_AptosCoin'_$memory, $account_address#$1_type_info_TypeInfo($1_type_info_TypeInfo(1, Vec(DefaultVecMap()[0 := 97][1 := 112][2 := 116][3 := 111][4 := 115][5 := 95][6 := 99][7 := 111][8 := 105][9 := 110], 10), Vec(DefaultVecMap()[0 := 65][1 := 112][2 := 116][3 := 111][4 := 115][5 := 67][6 := 111][7 := 105][8 := 110], 9))))));

    // $t15 := coin::value<aptos_coin::AptosCoin>($t13) on_abort goto L2 with $t2 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/stake.move:322:13+41
    assume {:print "$at(131,14563,14604)"} true;
    call $t15 := $1_coin_value'$1_aptos_coin_AptosCoin'($t13);
    if ($abort_flag) {
        assume {:print "$at(131,14563,14604)"} true;
        $t2 := $abort_code;
        assume {:print "$track_abort(38,22):", $t2} $t2 == $t2;
        goto L2;
    }

    // trace_return[0]($t6) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/stake.move:318:9+211
    assume {:print "$at(131,14404,14615)"} true;
    assume {:print "$track_return(38,22,0):", $t6} $t6 == $t6;

    // trace_return[1]($t9) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/stake.move:318:9+211
    assume {:print "$track_return(38,22,1):", $t9} $t9 == $t9;

    // trace_return[2]($t12) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/stake.move:318:9+211
    assume {:print "$track_return(38,22,2):", $t12} $t12 == $t12;

    // trace_return[3]($t15) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/stake.move:318:9+211
    assume {:print "$track_return(38,22,3):", $t15} $t15 == $t15;

    // label L1 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/stake.move:324:5+1
    assume {:print "$at(131,14620,14621)"} true;
L1:

    // return ($t6, $t9, $t12, $t15) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/stake.move:324:5+1
    assume {:print "$at(131,14620,14621)"} true;
    $ret0 := $t6;
    $ret1 := $t9;
    $ret2 := $t12;
    $ret3 := $t15;
    return;

    // label L2 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/stake.move:324:5+1
L2:

    // abort($t2) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/stake.move:324:5+1
    assume {:print "$at(131,14620,14621)"} true;
    $abort_code := $t2;
    $abort_flag := true;
    return;

}

// fun stake::stake_pool_exists [baseline] at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/stake.move:400:5+89
procedure {:inline 1} $1_stake_stake_pool_exists(_$t0: int) returns ($ret0: bool)
{
    // declare local variables
    var $t1: bool;
    var $t0: int;
    var $temp_0'address': int;
    var $temp_0'bool': bool;
    $t0 := _$t0;

    // bytecode translation starts here
    // trace_local[addr]($t0) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/stake.move:400:5+1
    assume {:print "$at(131,18212,18213)"} true;
    assume {:print "$track_local(38,47,0):", $t0} $t0 == $t0;

    // $t1 := exists<stake::StakePool>($t0) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/stake.move:401:9+6
    assume {:print "$at(131,18272,18278)"} true;
    $t1 := $ResourceExists($1_stake_StakePool_$memory, $t0);

    // trace_return[0]($t1) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/stake.move:401:9+23
    assume {:print "$track_return(38,47,0):", $t1} $t1 == $t1;

    // label L1 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/stake.move:402:5+1
    assume {:print "$at(131,18300,18301)"} true;
L1:

    // return $t1 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/stake.move:402:5+1
    assume {:print "$at(131,18300,18301)"} true;
    $ret0 := $t1;
    return;

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

// struct staking_contract::AddStakeEvent at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/staking_contract.move:129:5+122
type {:datatype} $1_staking_contract_AddStakeEvent;
function {:constructor} $1_staking_contract_AddStakeEvent($operator: int, $pool_address: int, $amount: int): $1_staking_contract_AddStakeEvent;
function {:inline} $Update'$1_staking_contract_AddStakeEvent'_operator(s: $1_staking_contract_AddStakeEvent, x: int): $1_staking_contract_AddStakeEvent {
    $1_staking_contract_AddStakeEvent(x, $pool_address#$1_staking_contract_AddStakeEvent(s), $amount#$1_staking_contract_AddStakeEvent(s))
}
function {:inline} $Update'$1_staking_contract_AddStakeEvent'_pool_address(s: $1_staking_contract_AddStakeEvent, x: int): $1_staking_contract_AddStakeEvent {
    $1_staking_contract_AddStakeEvent($operator#$1_staking_contract_AddStakeEvent(s), x, $amount#$1_staking_contract_AddStakeEvent(s))
}
function {:inline} $Update'$1_staking_contract_AddStakeEvent'_amount(s: $1_staking_contract_AddStakeEvent, x: int): $1_staking_contract_AddStakeEvent {
    $1_staking_contract_AddStakeEvent($operator#$1_staking_contract_AddStakeEvent(s), $pool_address#$1_staking_contract_AddStakeEvent(s), x)
}
function $IsValid'$1_staking_contract_AddStakeEvent'(s: $1_staking_contract_AddStakeEvent): bool {
    $IsValid'address'($operator#$1_staking_contract_AddStakeEvent(s))
      && $IsValid'address'($pool_address#$1_staking_contract_AddStakeEvent(s))
      && $IsValid'u64'($amount#$1_staking_contract_AddStakeEvent(s))
}
function {:inline} $IsEqual'$1_staking_contract_AddStakeEvent'(s1: $1_staking_contract_AddStakeEvent, s2: $1_staking_contract_AddStakeEvent): bool {
    s1 == s2
}

// struct staking_contract::UnlockStakeEvent at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/staking_contract.move:142:5+156
type {:datatype} $1_staking_contract_UnlockStakeEvent;
function {:constructor} $1_staking_contract_UnlockStakeEvent($operator: int, $pool_address: int, $amount: int, $commission_paid: int): $1_staking_contract_UnlockStakeEvent;
function {:inline} $Update'$1_staking_contract_UnlockStakeEvent'_operator(s: $1_staking_contract_UnlockStakeEvent, x: int): $1_staking_contract_UnlockStakeEvent {
    $1_staking_contract_UnlockStakeEvent(x, $pool_address#$1_staking_contract_UnlockStakeEvent(s), $amount#$1_staking_contract_UnlockStakeEvent(s), $commission_paid#$1_staking_contract_UnlockStakeEvent(s))
}
function {:inline} $Update'$1_staking_contract_UnlockStakeEvent'_pool_address(s: $1_staking_contract_UnlockStakeEvent, x: int): $1_staking_contract_UnlockStakeEvent {
    $1_staking_contract_UnlockStakeEvent($operator#$1_staking_contract_UnlockStakeEvent(s), x, $amount#$1_staking_contract_UnlockStakeEvent(s), $commission_paid#$1_staking_contract_UnlockStakeEvent(s))
}
function {:inline} $Update'$1_staking_contract_UnlockStakeEvent'_amount(s: $1_staking_contract_UnlockStakeEvent, x: int): $1_staking_contract_UnlockStakeEvent {
    $1_staking_contract_UnlockStakeEvent($operator#$1_staking_contract_UnlockStakeEvent(s), $pool_address#$1_staking_contract_UnlockStakeEvent(s), x, $commission_paid#$1_staking_contract_UnlockStakeEvent(s))
}
function {:inline} $Update'$1_staking_contract_UnlockStakeEvent'_commission_paid(s: $1_staking_contract_UnlockStakeEvent, x: int): $1_staking_contract_UnlockStakeEvent {
    $1_staking_contract_UnlockStakeEvent($operator#$1_staking_contract_UnlockStakeEvent(s), $pool_address#$1_staking_contract_UnlockStakeEvent(s), $amount#$1_staking_contract_UnlockStakeEvent(s), x)
}
function $IsValid'$1_staking_contract_UnlockStakeEvent'(s: $1_staking_contract_UnlockStakeEvent): bool {
    $IsValid'address'($operator#$1_staking_contract_UnlockStakeEvent(s))
      && $IsValid'address'($pool_address#$1_staking_contract_UnlockStakeEvent(s))
      && $IsValid'u64'($amount#$1_staking_contract_UnlockStakeEvent(s))
      && $IsValid'u64'($commission_paid#$1_staking_contract_UnlockStakeEvent(s))
}
function {:inline} $IsEqual'$1_staking_contract_UnlockStakeEvent'(s1: $1_staking_contract_UnlockStakeEvent, s2: $1_staking_contract_UnlockStakeEvent): bool {
    s1 == s2
}

// struct staking_contract::AddDistributionEvent at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/staking_contract.move:155:5+130
type {:datatype} $1_staking_contract_AddDistributionEvent;
function {:constructor} $1_staking_contract_AddDistributionEvent($operator: int, $pool_address: int, $amount: int): $1_staking_contract_AddDistributionEvent;
function {:inline} $Update'$1_staking_contract_AddDistributionEvent'_operator(s: $1_staking_contract_AddDistributionEvent, x: int): $1_staking_contract_AddDistributionEvent {
    $1_staking_contract_AddDistributionEvent(x, $pool_address#$1_staking_contract_AddDistributionEvent(s), $amount#$1_staking_contract_AddDistributionEvent(s))
}
function {:inline} $Update'$1_staking_contract_AddDistributionEvent'_pool_address(s: $1_staking_contract_AddDistributionEvent, x: int): $1_staking_contract_AddDistributionEvent {
    $1_staking_contract_AddDistributionEvent($operator#$1_staking_contract_AddDistributionEvent(s), x, $amount#$1_staking_contract_AddDistributionEvent(s))
}
function {:inline} $Update'$1_staking_contract_AddDistributionEvent'_amount(s: $1_staking_contract_AddDistributionEvent, x: int): $1_staking_contract_AddDistributionEvent {
    $1_staking_contract_AddDistributionEvent($operator#$1_staking_contract_AddDistributionEvent(s), $pool_address#$1_staking_contract_AddDistributionEvent(s), x)
}
function $IsValid'$1_staking_contract_AddDistributionEvent'(s: $1_staking_contract_AddDistributionEvent): bool {
    $IsValid'address'($operator#$1_staking_contract_AddDistributionEvent(s))
      && $IsValid'address'($pool_address#$1_staking_contract_AddDistributionEvent(s))
      && $IsValid'u64'($amount#$1_staking_contract_AddDistributionEvent(s))
}
function {:inline} $IsEqual'$1_staking_contract_AddDistributionEvent'(s1: $1_staking_contract_AddDistributionEvent, s2: $1_staking_contract_AddDistributionEvent): bool {
    s1 == s2
}

// struct staking_contract::CreateStakingContractEvent at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/staking_contract.move:109:5+199
type {:datatype} $1_staking_contract_CreateStakingContractEvent;
function {:constructor} $1_staking_contract_CreateStakingContractEvent($operator: int, $voter: int, $pool_address: int, $principal: int, $commission_percentage: int): $1_staking_contract_CreateStakingContractEvent;
function {:inline} $Update'$1_staking_contract_CreateStakingContractEvent'_operator(s: $1_staking_contract_CreateStakingContractEvent, x: int): $1_staking_contract_CreateStakingContractEvent {
    $1_staking_contract_CreateStakingContractEvent(x, $voter#$1_staking_contract_CreateStakingContractEvent(s), $pool_address#$1_staking_contract_CreateStakingContractEvent(s), $principal#$1_staking_contract_CreateStakingContractEvent(s), $commission_percentage#$1_staking_contract_CreateStakingContractEvent(s))
}
function {:inline} $Update'$1_staking_contract_CreateStakingContractEvent'_voter(s: $1_staking_contract_CreateStakingContractEvent, x: int): $1_staking_contract_CreateStakingContractEvent {
    $1_staking_contract_CreateStakingContractEvent($operator#$1_staking_contract_CreateStakingContractEvent(s), x, $pool_address#$1_staking_contract_CreateStakingContractEvent(s), $principal#$1_staking_contract_CreateStakingContractEvent(s), $commission_percentage#$1_staking_contract_CreateStakingContractEvent(s))
}
function {:inline} $Update'$1_staking_contract_CreateStakingContractEvent'_pool_address(s: $1_staking_contract_CreateStakingContractEvent, x: int): $1_staking_contract_CreateStakingContractEvent {
    $1_staking_contract_CreateStakingContractEvent($operator#$1_staking_contract_CreateStakingContractEvent(s), $voter#$1_staking_contract_CreateStakingContractEvent(s), x, $principal#$1_staking_contract_CreateStakingContractEvent(s), $commission_percentage#$1_staking_contract_CreateStakingContractEvent(s))
}
function {:inline} $Update'$1_staking_contract_CreateStakingContractEvent'_principal(s: $1_staking_contract_CreateStakingContractEvent, x: int): $1_staking_contract_CreateStakingContractEvent {
    $1_staking_contract_CreateStakingContractEvent($operator#$1_staking_contract_CreateStakingContractEvent(s), $voter#$1_staking_contract_CreateStakingContractEvent(s), $pool_address#$1_staking_contract_CreateStakingContractEvent(s), x, $commission_percentage#$1_staking_contract_CreateStakingContractEvent(s))
}
function {:inline} $Update'$1_staking_contract_CreateStakingContractEvent'_commission_percentage(s: $1_staking_contract_CreateStakingContractEvent, x: int): $1_staking_contract_CreateStakingContractEvent {
    $1_staking_contract_CreateStakingContractEvent($operator#$1_staking_contract_CreateStakingContractEvent(s), $voter#$1_staking_contract_CreateStakingContractEvent(s), $pool_address#$1_staking_contract_CreateStakingContractEvent(s), $principal#$1_staking_contract_CreateStakingContractEvent(s), x)
}
function $IsValid'$1_staking_contract_CreateStakingContractEvent'(s: $1_staking_contract_CreateStakingContractEvent): bool {
    $IsValid'address'($operator#$1_staking_contract_CreateStakingContractEvent(s))
      && $IsValid'address'($voter#$1_staking_contract_CreateStakingContractEvent(s))
      && $IsValid'address'($pool_address#$1_staking_contract_CreateStakingContractEvent(s))
      && $IsValid'u64'($principal#$1_staking_contract_CreateStakingContractEvent(s))
      && $IsValid'u64'($commission_percentage#$1_staking_contract_CreateStakingContractEvent(s))
}
function {:inline} $IsEqual'$1_staking_contract_CreateStakingContractEvent'(s1: $1_staking_contract_CreateStakingContractEvent, s2: $1_staking_contract_CreateStakingContractEvent): bool {
    s1 == s2
}

// struct staking_contract::DistributeEvent at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/staking_contract.move:161:5+153
type {:datatype} $1_staking_contract_DistributeEvent;
function {:constructor} $1_staking_contract_DistributeEvent($operator: int, $pool_address: int, $recipient: int, $amount: int): $1_staking_contract_DistributeEvent;
function {:inline} $Update'$1_staking_contract_DistributeEvent'_operator(s: $1_staking_contract_DistributeEvent, x: int): $1_staking_contract_DistributeEvent {
    $1_staking_contract_DistributeEvent(x, $pool_address#$1_staking_contract_DistributeEvent(s), $recipient#$1_staking_contract_DistributeEvent(s), $amount#$1_staking_contract_DistributeEvent(s))
}
function {:inline} $Update'$1_staking_contract_DistributeEvent'_pool_address(s: $1_staking_contract_DistributeEvent, x: int): $1_staking_contract_DistributeEvent {
    $1_staking_contract_DistributeEvent($operator#$1_staking_contract_DistributeEvent(s), x, $recipient#$1_staking_contract_DistributeEvent(s), $amount#$1_staking_contract_DistributeEvent(s))
}
function {:inline} $Update'$1_staking_contract_DistributeEvent'_recipient(s: $1_staking_contract_DistributeEvent, x: int): $1_staking_contract_DistributeEvent {
    $1_staking_contract_DistributeEvent($operator#$1_staking_contract_DistributeEvent(s), $pool_address#$1_staking_contract_DistributeEvent(s), x, $amount#$1_staking_contract_DistributeEvent(s))
}
function {:inline} $Update'$1_staking_contract_DistributeEvent'_amount(s: $1_staking_contract_DistributeEvent, x: int): $1_staking_contract_DistributeEvent {
    $1_staking_contract_DistributeEvent($operator#$1_staking_contract_DistributeEvent(s), $pool_address#$1_staking_contract_DistributeEvent(s), $recipient#$1_staking_contract_DistributeEvent(s), x)
}
function $IsValid'$1_staking_contract_DistributeEvent'(s: $1_staking_contract_DistributeEvent): bool {
    $IsValid'address'($operator#$1_staking_contract_DistributeEvent(s))
      && $IsValid'address'($pool_address#$1_staking_contract_DistributeEvent(s))
      && $IsValid'address'($recipient#$1_staking_contract_DistributeEvent(s))
      && $IsValid'u64'($amount#$1_staking_contract_DistributeEvent(s))
}
function {:inline} $IsEqual'$1_staking_contract_DistributeEvent'(s1: $1_staking_contract_DistributeEvent, s2: $1_staking_contract_DistributeEvent): bool {
    s1 == s2
}

// struct staking_contract::RequestCommissionEvent at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/staking_contract.move:135:5+177
type {:datatype} $1_staking_contract_RequestCommissionEvent;
function {:constructor} $1_staking_contract_RequestCommissionEvent($operator: int, $pool_address: int, $accumulated_rewards: int, $commission_amount: int): $1_staking_contract_RequestCommissionEvent;
function {:inline} $Update'$1_staking_contract_RequestCommissionEvent'_operator(s: $1_staking_contract_RequestCommissionEvent, x: int): $1_staking_contract_RequestCommissionEvent {
    $1_staking_contract_RequestCommissionEvent(x, $pool_address#$1_staking_contract_RequestCommissionEvent(s), $accumulated_rewards#$1_staking_contract_RequestCommissionEvent(s), $commission_amount#$1_staking_contract_RequestCommissionEvent(s))
}
function {:inline} $Update'$1_staking_contract_RequestCommissionEvent'_pool_address(s: $1_staking_contract_RequestCommissionEvent, x: int): $1_staking_contract_RequestCommissionEvent {
    $1_staking_contract_RequestCommissionEvent($operator#$1_staking_contract_RequestCommissionEvent(s), x, $accumulated_rewards#$1_staking_contract_RequestCommissionEvent(s), $commission_amount#$1_staking_contract_RequestCommissionEvent(s))
}
function {:inline} $Update'$1_staking_contract_RequestCommissionEvent'_accumulated_rewards(s: $1_staking_contract_RequestCommissionEvent, x: int): $1_staking_contract_RequestCommissionEvent {
    $1_staking_contract_RequestCommissionEvent($operator#$1_staking_contract_RequestCommissionEvent(s), $pool_address#$1_staking_contract_RequestCommissionEvent(s), x, $commission_amount#$1_staking_contract_RequestCommissionEvent(s))
}
function {:inline} $Update'$1_staking_contract_RequestCommissionEvent'_commission_amount(s: $1_staking_contract_RequestCommissionEvent, x: int): $1_staking_contract_RequestCommissionEvent {
    $1_staking_contract_RequestCommissionEvent($operator#$1_staking_contract_RequestCommissionEvent(s), $pool_address#$1_staking_contract_RequestCommissionEvent(s), $accumulated_rewards#$1_staking_contract_RequestCommissionEvent(s), x)
}
function $IsValid'$1_staking_contract_RequestCommissionEvent'(s: $1_staking_contract_RequestCommissionEvent): bool {
    $IsValid'address'($operator#$1_staking_contract_RequestCommissionEvent(s))
      && $IsValid'address'($pool_address#$1_staking_contract_RequestCommissionEvent(s))
      && $IsValid'u64'($accumulated_rewards#$1_staking_contract_RequestCommissionEvent(s))
      && $IsValid'u64'($commission_amount#$1_staking_contract_RequestCommissionEvent(s))
}
function {:inline} $IsEqual'$1_staking_contract_RequestCommissionEvent'(s1: $1_staking_contract_RequestCommissionEvent, s2: $1_staking_contract_RequestCommissionEvent): bool {
    s1 == s2
}

// struct staking_contract::ResetLockupEvent at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/staking_contract.move:124:5+105
type {:datatype} $1_staking_contract_ResetLockupEvent;
function {:constructor} $1_staking_contract_ResetLockupEvent($operator: int, $pool_address: int): $1_staking_contract_ResetLockupEvent;
function {:inline} $Update'$1_staking_contract_ResetLockupEvent'_operator(s: $1_staking_contract_ResetLockupEvent, x: int): $1_staking_contract_ResetLockupEvent {
    $1_staking_contract_ResetLockupEvent(x, $pool_address#$1_staking_contract_ResetLockupEvent(s))
}
function {:inline} $Update'$1_staking_contract_ResetLockupEvent'_pool_address(s: $1_staking_contract_ResetLockupEvent, x: int): $1_staking_contract_ResetLockupEvent {
    $1_staking_contract_ResetLockupEvent($operator#$1_staking_contract_ResetLockupEvent(s), x)
}
function $IsValid'$1_staking_contract_ResetLockupEvent'(s: $1_staking_contract_ResetLockupEvent): bool {
    $IsValid'address'($operator#$1_staking_contract_ResetLockupEvent(s))
      && $IsValid'address'($pool_address#$1_staking_contract_ResetLockupEvent(s))
}
function {:inline} $IsEqual'$1_staking_contract_ResetLockupEvent'(s1: $1_staking_contract_ResetLockupEvent, s2: $1_staking_contract_ResetLockupEvent): bool {
    s1 == s2
}

// struct staking_contract::StakingContract at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/staking_contract.move:68:5+692
type {:datatype} $1_staking_contract_StakingContract;
function {:constructor} $1_staking_contract_StakingContract($principal: int, $pool_address: int, $owner_cap: $1_stake_OwnerCapability, $commission_percentage: int, $distribution_pool: $1_pool_u64_Pool, $signer_cap: $1_account_SignerCapability): $1_staking_contract_StakingContract;
function {:inline} $Update'$1_staking_contract_StakingContract'_principal(s: $1_staking_contract_StakingContract, x: int): $1_staking_contract_StakingContract {
    $1_staking_contract_StakingContract(x, $pool_address#$1_staking_contract_StakingContract(s), $owner_cap#$1_staking_contract_StakingContract(s), $commission_percentage#$1_staking_contract_StakingContract(s), $distribution_pool#$1_staking_contract_StakingContract(s), $signer_cap#$1_staking_contract_StakingContract(s))
}
function {:inline} $Update'$1_staking_contract_StakingContract'_pool_address(s: $1_staking_contract_StakingContract, x: int): $1_staking_contract_StakingContract {
    $1_staking_contract_StakingContract($principal#$1_staking_contract_StakingContract(s), x, $owner_cap#$1_staking_contract_StakingContract(s), $commission_percentage#$1_staking_contract_StakingContract(s), $distribution_pool#$1_staking_contract_StakingContract(s), $signer_cap#$1_staking_contract_StakingContract(s))
}
function {:inline} $Update'$1_staking_contract_StakingContract'_owner_cap(s: $1_staking_contract_StakingContract, x: $1_stake_OwnerCapability): $1_staking_contract_StakingContract {
    $1_staking_contract_StakingContract($principal#$1_staking_contract_StakingContract(s), $pool_address#$1_staking_contract_StakingContract(s), x, $commission_percentage#$1_staking_contract_StakingContract(s), $distribution_pool#$1_staking_contract_StakingContract(s), $signer_cap#$1_staking_contract_StakingContract(s))
}
function {:inline} $Update'$1_staking_contract_StakingContract'_commission_percentage(s: $1_staking_contract_StakingContract, x: int): $1_staking_contract_StakingContract {
    $1_staking_contract_StakingContract($principal#$1_staking_contract_StakingContract(s), $pool_address#$1_staking_contract_StakingContract(s), $owner_cap#$1_staking_contract_StakingContract(s), x, $distribution_pool#$1_staking_contract_StakingContract(s), $signer_cap#$1_staking_contract_StakingContract(s))
}
function {:inline} $Update'$1_staking_contract_StakingContract'_distribution_pool(s: $1_staking_contract_StakingContract, x: $1_pool_u64_Pool): $1_staking_contract_StakingContract {
    $1_staking_contract_StakingContract($principal#$1_staking_contract_StakingContract(s), $pool_address#$1_staking_contract_StakingContract(s), $owner_cap#$1_staking_contract_StakingContract(s), $commission_percentage#$1_staking_contract_StakingContract(s), x, $signer_cap#$1_staking_contract_StakingContract(s))
}
function {:inline} $Update'$1_staking_contract_StakingContract'_signer_cap(s: $1_staking_contract_StakingContract, x: $1_account_SignerCapability): $1_staking_contract_StakingContract {
    $1_staking_contract_StakingContract($principal#$1_staking_contract_StakingContract(s), $pool_address#$1_staking_contract_StakingContract(s), $owner_cap#$1_staking_contract_StakingContract(s), $commission_percentage#$1_staking_contract_StakingContract(s), $distribution_pool#$1_staking_contract_StakingContract(s), x)
}
function $IsValid'$1_staking_contract_StakingContract'(s: $1_staking_contract_StakingContract): bool {
    $IsValid'u64'($principal#$1_staking_contract_StakingContract(s))
      && $IsValid'address'($pool_address#$1_staking_contract_StakingContract(s))
      && $IsValid'$1_stake_OwnerCapability'($owner_cap#$1_staking_contract_StakingContract(s))
      && $IsValid'u64'($commission_percentage#$1_staking_contract_StakingContract(s))
      && $IsValid'$1_pool_u64_Pool'($distribution_pool#$1_staking_contract_StakingContract(s))
      && $IsValid'$1_account_SignerCapability'($signer_cap#$1_staking_contract_StakingContract(s))
}
function {:inline} $IsEqual'$1_staking_contract_StakingContract'(s1: $1_staking_contract_StakingContract, s2: $1_staking_contract_StakingContract): bool {
    $IsEqual'u64'($principal#$1_staking_contract_StakingContract(s1), $principal#$1_staking_contract_StakingContract(s2))
    && $IsEqual'address'($pool_address#$1_staking_contract_StakingContract(s1), $pool_address#$1_staking_contract_StakingContract(s2))
    && $IsEqual'$1_stake_OwnerCapability'($owner_cap#$1_staking_contract_StakingContract(s1), $owner_cap#$1_staking_contract_StakingContract(s2))
    && $IsEqual'u64'($commission_percentage#$1_staking_contract_StakingContract(s1), $commission_percentage#$1_staking_contract_StakingContract(s2))
    && $IsEqual'$1_pool_u64_Pool'($distribution_pool#$1_staking_contract_StakingContract(s1), $distribution_pool#$1_staking_contract_StakingContract(s2))
    && $IsEqual'$1_account_SignerCapability'($signer_cap#$1_staking_contract_StakingContract(s1), $signer_cap#$1_staking_contract_StakingContract(s2))}

// struct staking_contract::Store at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/staking_contract.move:82:5+690
type {:datatype} $1_staking_contract_Store;
function {:constructor} $1_staking_contract_Store($staking_contracts: Table int ($1_staking_contract_StakingContract), $create_staking_contract_events: $1_event_EventHandle'$1_staking_contract_CreateStakingContractEvent', $update_voter_events: $1_event_EventHandle'$1_staking_contract_UpdateVoterEvent', $reset_lockup_events: $1_event_EventHandle'$1_staking_contract_ResetLockupEvent', $add_stake_events: $1_event_EventHandle'$1_staking_contract_AddStakeEvent', $request_commission_events: $1_event_EventHandle'$1_staking_contract_RequestCommissionEvent', $unlock_stake_events: $1_event_EventHandle'$1_staking_contract_UnlockStakeEvent', $switch_operator_events: $1_event_EventHandle'$1_staking_contract_SwitchOperatorEvent', $add_distribution_events: $1_event_EventHandle'$1_staking_contract_AddDistributionEvent', $distribute_events: $1_event_EventHandle'$1_staking_contract_DistributeEvent'): $1_staking_contract_Store;
function {:inline} $Update'$1_staking_contract_Store'_staking_contracts(s: $1_staking_contract_Store, x: Table int ($1_staking_contract_StakingContract)): $1_staking_contract_Store {
    $1_staking_contract_Store(x, $create_staking_contract_events#$1_staking_contract_Store(s), $update_voter_events#$1_staking_contract_Store(s), $reset_lockup_events#$1_staking_contract_Store(s), $add_stake_events#$1_staking_contract_Store(s), $request_commission_events#$1_staking_contract_Store(s), $unlock_stake_events#$1_staking_contract_Store(s), $switch_operator_events#$1_staking_contract_Store(s), $add_distribution_events#$1_staking_contract_Store(s), $distribute_events#$1_staking_contract_Store(s))
}
function {:inline} $Update'$1_staking_contract_Store'_create_staking_contract_events(s: $1_staking_contract_Store, x: $1_event_EventHandle'$1_staking_contract_CreateStakingContractEvent'): $1_staking_contract_Store {
    $1_staking_contract_Store($staking_contracts#$1_staking_contract_Store(s), x, $update_voter_events#$1_staking_contract_Store(s), $reset_lockup_events#$1_staking_contract_Store(s), $add_stake_events#$1_staking_contract_Store(s), $request_commission_events#$1_staking_contract_Store(s), $unlock_stake_events#$1_staking_contract_Store(s), $switch_operator_events#$1_staking_contract_Store(s), $add_distribution_events#$1_staking_contract_Store(s), $distribute_events#$1_staking_contract_Store(s))
}
function {:inline} $Update'$1_staking_contract_Store'_update_voter_events(s: $1_staking_contract_Store, x: $1_event_EventHandle'$1_staking_contract_UpdateVoterEvent'): $1_staking_contract_Store {
    $1_staking_contract_Store($staking_contracts#$1_staking_contract_Store(s), $create_staking_contract_events#$1_staking_contract_Store(s), x, $reset_lockup_events#$1_staking_contract_Store(s), $add_stake_events#$1_staking_contract_Store(s), $request_commission_events#$1_staking_contract_Store(s), $unlock_stake_events#$1_staking_contract_Store(s), $switch_operator_events#$1_staking_contract_Store(s), $add_distribution_events#$1_staking_contract_Store(s), $distribute_events#$1_staking_contract_Store(s))
}
function {:inline} $Update'$1_staking_contract_Store'_reset_lockup_events(s: $1_staking_contract_Store, x: $1_event_EventHandle'$1_staking_contract_ResetLockupEvent'): $1_staking_contract_Store {
    $1_staking_contract_Store($staking_contracts#$1_staking_contract_Store(s), $create_staking_contract_events#$1_staking_contract_Store(s), $update_voter_events#$1_staking_contract_Store(s), x, $add_stake_events#$1_staking_contract_Store(s), $request_commission_events#$1_staking_contract_Store(s), $unlock_stake_events#$1_staking_contract_Store(s), $switch_operator_events#$1_staking_contract_Store(s), $add_distribution_events#$1_staking_contract_Store(s), $distribute_events#$1_staking_contract_Store(s))
}
function {:inline} $Update'$1_staking_contract_Store'_add_stake_events(s: $1_staking_contract_Store, x: $1_event_EventHandle'$1_staking_contract_AddStakeEvent'): $1_staking_contract_Store {
    $1_staking_contract_Store($staking_contracts#$1_staking_contract_Store(s), $create_staking_contract_events#$1_staking_contract_Store(s), $update_voter_events#$1_staking_contract_Store(s), $reset_lockup_events#$1_staking_contract_Store(s), x, $request_commission_events#$1_staking_contract_Store(s), $unlock_stake_events#$1_staking_contract_Store(s), $switch_operator_events#$1_staking_contract_Store(s), $add_distribution_events#$1_staking_contract_Store(s), $distribute_events#$1_staking_contract_Store(s))
}
function {:inline} $Update'$1_staking_contract_Store'_request_commission_events(s: $1_staking_contract_Store, x: $1_event_EventHandle'$1_staking_contract_RequestCommissionEvent'): $1_staking_contract_Store {
    $1_staking_contract_Store($staking_contracts#$1_staking_contract_Store(s), $create_staking_contract_events#$1_staking_contract_Store(s), $update_voter_events#$1_staking_contract_Store(s), $reset_lockup_events#$1_staking_contract_Store(s), $add_stake_events#$1_staking_contract_Store(s), x, $unlock_stake_events#$1_staking_contract_Store(s), $switch_operator_events#$1_staking_contract_Store(s), $add_distribution_events#$1_staking_contract_Store(s), $distribute_events#$1_staking_contract_Store(s))
}
function {:inline} $Update'$1_staking_contract_Store'_unlock_stake_events(s: $1_staking_contract_Store, x: $1_event_EventHandle'$1_staking_contract_UnlockStakeEvent'): $1_staking_contract_Store {
    $1_staking_contract_Store($staking_contracts#$1_staking_contract_Store(s), $create_staking_contract_events#$1_staking_contract_Store(s), $update_voter_events#$1_staking_contract_Store(s), $reset_lockup_events#$1_staking_contract_Store(s), $add_stake_events#$1_staking_contract_Store(s), $request_commission_events#$1_staking_contract_Store(s), x, $switch_operator_events#$1_staking_contract_Store(s), $add_distribution_events#$1_staking_contract_Store(s), $distribute_events#$1_staking_contract_Store(s))
}
function {:inline} $Update'$1_staking_contract_Store'_switch_operator_events(s: $1_staking_contract_Store, x: $1_event_EventHandle'$1_staking_contract_SwitchOperatorEvent'): $1_staking_contract_Store {
    $1_staking_contract_Store($staking_contracts#$1_staking_contract_Store(s), $create_staking_contract_events#$1_staking_contract_Store(s), $update_voter_events#$1_staking_contract_Store(s), $reset_lockup_events#$1_staking_contract_Store(s), $add_stake_events#$1_staking_contract_Store(s), $request_commission_events#$1_staking_contract_Store(s), $unlock_stake_events#$1_staking_contract_Store(s), x, $add_distribution_events#$1_staking_contract_Store(s), $distribute_events#$1_staking_contract_Store(s))
}
function {:inline} $Update'$1_staking_contract_Store'_add_distribution_events(s: $1_staking_contract_Store, x: $1_event_EventHandle'$1_staking_contract_AddDistributionEvent'): $1_staking_contract_Store {
    $1_staking_contract_Store($staking_contracts#$1_staking_contract_Store(s), $create_staking_contract_events#$1_staking_contract_Store(s), $update_voter_events#$1_staking_contract_Store(s), $reset_lockup_events#$1_staking_contract_Store(s), $add_stake_events#$1_staking_contract_Store(s), $request_commission_events#$1_staking_contract_Store(s), $unlock_stake_events#$1_staking_contract_Store(s), $switch_operator_events#$1_staking_contract_Store(s), x, $distribute_events#$1_staking_contract_Store(s))
}
function {:inline} $Update'$1_staking_contract_Store'_distribute_events(s: $1_staking_contract_Store, x: $1_event_EventHandle'$1_staking_contract_DistributeEvent'): $1_staking_contract_Store {
    $1_staking_contract_Store($staking_contracts#$1_staking_contract_Store(s), $create_staking_contract_events#$1_staking_contract_Store(s), $update_voter_events#$1_staking_contract_Store(s), $reset_lockup_events#$1_staking_contract_Store(s), $add_stake_events#$1_staking_contract_Store(s), $request_commission_events#$1_staking_contract_Store(s), $unlock_stake_events#$1_staking_contract_Store(s), $switch_operator_events#$1_staking_contract_Store(s), $add_distribution_events#$1_staking_contract_Store(s), x)
}
function $IsValid'$1_staking_contract_Store'(s: $1_staking_contract_Store): bool {
    $IsValid'$1_simple_map_SimpleMap'address_$1_staking_contract_StakingContract''($staking_contracts#$1_staking_contract_Store(s))
      && $IsValid'$1_event_EventHandle'$1_staking_contract_CreateStakingContractEvent''($create_staking_contract_events#$1_staking_contract_Store(s))
      && $IsValid'$1_event_EventHandle'$1_staking_contract_UpdateVoterEvent''($update_voter_events#$1_staking_contract_Store(s))
      && $IsValid'$1_event_EventHandle'$1_staking_contract_ResetLockupEvent''($reset_lockup_events#$1_staking_contract_Store(s))
      && $IsValid'$1_event_EventHandle'$1_staking_contract_AddStakeEvent''($add_stake_events#$1_staking_contract_Store(s))
      && $IsValid'$1_event_EventHandle'$1_staking_contract_RequestCommissionEvent''($request_commission_events#$1_staking_contract_Store(s))
      && $IsValid'$1_event_EventHandle'$1_staking_contract_UnlockStakeEvent''($unlock_stake_events#$1_staking_contract_Store(s))
      && $IsValid'$1_event_EventHandle'$1_staking_contract_SwitchOperatorEvent''($switch_operator_events#$1_staking_contract_Store(s))
      && $IsValid'$1_event_EventHandle'$1_staking_contract_AddDistributionEvent''($add_distribution_events#$1_staking_contract_Store(s))
      && $IsValid'$1_event_EventHandle'$1_staking_contract_DistributeEvent''($distribute_events#$1_staking_contract_Store(s))
}
function {:inline} $IsEqual'$1_staking_contract_Store'(s1: $1_staking_contract_Store, s2: $1_staking_contract_Store): bool {
    $IsEqual'$1_simple_map_SimpleMap'address_$1_staking_contract_StakingContract''($staking_contracts#$1_staking_contract_Store(s1), $staking_contracts#$1_staking_contract_Store(s2))
    && $IsEqual'$1_event_EventHandle'$1_staking_contract_CreateStakingContractEvent''($create_staking_contract_events#$1_staking_contract_Store(s1), $create_staking_contract_events#$1_staking_contract_Store(s2))
    && $IsEqual'$1_event_EventHandle'$1_staking_contract_UpdateVoterEvent''($update_voter_events#$1_staking_contract_Store(s1), $update_voter_events#$1_staking_contract_Store(s2))
    && $IsEqual'$1_event_EventHandle'$1_staking_contract_ResetLockupEvent''($reset_lockup_events#$1_staking_contract_Store(s1), $reset_lockup_events#$1_staking_contract_Store(s2))
    && $IsEqual'$1_event_EventHandle'$1_staking_contract_AddStakeEvent''($add_stake_events#$1_staking_contract_Store(s1), $add_stake_events#$1_staking_contract_Store(s2))
    && $IsEqual'$1_event_EventHandle'$1_staking_contract_RequestCommissionEvent''($request_commission_events#$1_staking_contract_Store(s1), $request_commission_events#$1_staking_contract_Store(s2))
    && $IsEqual'$1_event_EventHandle'$1_staking_contract_UnlockStakeEvent''($unlock_stake_events#$1_staking_contract_Store(s1), $unlock_stake_events#$1_staking_contract_Store(s2))
    && $IsEqual'$1_event_EventHandle'$1_staking_contract_SwitchOperatorEvent''($switch_operator_events#$1_staking_contract_Store(s1), $switch_operator_events#$1_staking_contract_Store(s2))
    && $IsEqual'$1_event_EventHandle'$1_staking_contract_AddDistributionEvent''($add_distribution_events#$1_staking_contract_Store(s1), $add_distribution_events#$1_staking_contract_Store(s2))
    && $IsEqual'$1_event_EventHandle'$1_staking_contract_DistributeEvent''($distribute_events#$1_staking_contract_Store(s1), $distribute_events#$1_staking_contract_Store(s2))}
var $1_staking_contract_Store_$memory: $Memory $1_staking_contract_Store;

// struct staking_contract::SwitchOperatorEvent at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/staking_contract.move:149:5+143
type {:datatype} $1_staking_contract_SwitchOperatorEvent;
function {:constructor} $1_staking_contract_SwitchOperatorEvent($old_operator: int, $new_operator: int, $pool_address: int): $1_staking_contract_SwitchOperatorEvent;
function {:inline} $Update'$1_staking_contract_SwitchOperatorEvent'_old_operator(s: $1_staking_contract_SwitchOperatorEvent, x: int): $1_staking_contract_SwitchOperatorEvent {
    $1_staking_contract_SwitchOperatorEvent(x, $new_operator#$1_staking_contract_SwitchOperatorEvent(s), $pool_address#$1_staking_contract_SwitchOperatorEvent(s))
}
function {:inline} $Update'$1_staking_contract_SwitchOperatorEvent'_new_operator(s: $1_staking_contract_SwitchOperatorEvent, x: int): $1_staking_contract_SwitchOperatorEvent {
    $1_staking_contract_SwitchOperatorEvent($old_operator#$1_staking_contract_SwitchOperatorEvent(s), x, $pool_address#$1_staking_contract_SwitchOperatorEvent(s))
}
function {:inline} $Update'$1_staking_contract_SwitchOperatorEvent'_pool_address(s: $1_staking_contract_SwitchOperatorEvent, x: int): $1_staking_contract_SwitchOperatorEvent {
    $1_staking_contract_SwitchOperatorEvent($old_operator#$1_staking_contract_SwitchOperatorEvent(s), $new_operator#$1_staking_contract_SwitchOperatorEvent(s), x)
}
function $IsValid'$1_staking_contract_SwitchOperatorEvent'(s: $1_staking_contract_SwitchOperatorEvent): bool {
    $IsValid'address'($old_operator#$1_staking_contract_SwitchOperatorEvent(s))
      && $IsValid'address'($new_operator#$1_staking_contract_SwitchOperatorEvent(s))
      && $IsValid'address'($pool_address#$1_staking_contract_SwitchOperatorEvent(s))
}
function {:inline} $IsEqual'$1_staking_contract_SwitchOperatorEvent'(s1: $1_staking_contract_SwitchOperatorEvent, s2: $1_staking_contract_SwitchOperatorEvent): bool {
    s1 == s2
}

// struct staking_contract::UpdateVoterEvent at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/staking_contract.move:117:5+161
type {:datatype} $1_staking_contract_UpdateVoterEvent;
function {:constructor} $1_staking_contract_UpdateVoterEvent($operator: int, $pool_address: int, $old_voter: int, $new_voter: int): $1_staking_contract_UpdateVoterEvent;
function {:inline} $Update'$1_staking_contract_UpdateVoterEvent'_operator(s: $1_staking_contract_UpdateVoterEvent, x: int): $1_staking_contract_UpdateVoterEvent {
    $1_staking_contract_UpdateVoterEvent(x, $pool_address#$1_staking_contract_UpdateVoterEvent(s), $old_voter#$1_staking_contract_UpdateVoterEvent(s), $new_voter#$1_staking_contract_UpdateVoterEvent(s))
}
function {:inline} $Update'$1_staking_contract_UpdateVoterEvent'_pool_address(s: $1_staking_contract_UpdateVoterEvent, x: int): $1_staking_contract_UpdateVoterEvent {
    $1_staking_contract_UpdateVoterEvent($operator#$1_staking_contract_UpdateVoterEvent(s), x, $old_voter#$1_staking_contract_UpdateVoterEvent(s), $new_voter#$1_staking_contract_UpdateVoterEvent(s))
}
function {:inline} $Update'$1_staking_contract_UpdateVoterEvent'_old_voter(s: $1_staking_contract_UpdateVoterEvent, x: int): $1_staking_contract_UpdateVoterEvent {
    $1_staking_contract_UpdateVoterEvent($operator#$1_staking_contract_UpdateVoterEvent(s), $pool_address#$1_staking_contract_UpdateVoterEvent(s), x, $new_voter#$1_staking_contract_UpdateVoterEvent(s))
}
function {:inline} $Update'$1_staking_contract_UpdateVoterEvent'_new_voter(s: $1_staking_contract_UpdateVoterEvent, x: int): $1_staking_contract_UpdateVoterEvent {
    $1_staking_contract_UpdateVoterEvent($operator#$1_staking_contract_UpdateVoterEvent(s), $pool_address#$1_staking_contract_UpdateVoterEvent(s), $old_voter#$1_staking_contract_UpdateVoterEvent(s), x)
}
function $IsValid'$1_staking_contract_UpdateVoterEvent'(s: $1_staking_contract_UpdateVoterEvent): bool {
    $IsValid'address'($operator#$1_staking_contract_UpdateVoterEvent(s))
      && $IsValid'address'($pool_address#$1_staking_contract_UpdateVoterEvent(s))
      && $IsValid'address'($old_voter#$1_staking_contract_UpdateVoterEvent(s))
      && $IsValid'address'($new_voter#$1_staking_contract_UpdateVoterEvent(s))
}
function {:inline} $IsEqual'$1_staking_contract_UpdateVoterEvent'(s1: $1_staking_contract_UpdateVoterEvent, s2: $1_staking_contract_UpdateVoterEvent): bool {
    s1 == s2
}

// fun staking_contract::assert_staking_contract_exists [baseline] at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/staking_contract.move:622:5+446
procedure {:inline 1} $1_staking_contract_assert_staking_contract_exists(_$t0: int, _$t1: int) returns ()
{
    // declare local variables
    var $t2: int;
    var $t3: Table int ($1_staking_contract_StakingContract);
    var $t4: bool;
    var $t5: int;
    var $t6: int;
    var $t7: int;
    var $t8: $Mutation ($1_staking_contract_Store);
    var $t9: $Mutation (Table int ($1_staking_contract_StakingContract));
    var $t10: Table int ($1_staking_contract_StakingContract);
    var $t11: bool;
    var $t12: int;
    var $t13: int;
    var $t0: int;
    var $t1: int;
    var $temp_0'address': int;
    $t0 := _$t0;
    $t1 := _$t1;

    // bytecode translation starts here
    // assume Identical($t3, select staking_contract::Store.staking_contracts(global<staking_contract::Store>($t0))) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/staking_contract.spec.move:307:9+64
    assume {:print "$at(3,12992,13056)"} true;
    assume ($t3 == $staking_contracts#$1_staking_contract_Store($ResourceValue($1_staking_contract_Store_$memory, $t0)));

    // trace_local[staker]($t0) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/staking_contract.move:622:5+1
    assume {:print "$at(2,29541,29542)"} true;
    assume {:print "$track_local(56,2,0):", $t0} $t0 == $t0;

    // trace_local[operator]($t1) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/staking_contract.move:622:5+1
    assume {:print "$track_local(56,2,1):", $t1} $t1 == $t1;

    // $t4 := exists<staking_contract::Store>($t0) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/staking_contract.move:623:17+6
    assume {:print "$at(2,29645,29651)"} true;
    $t4 := $ResourceExists($1_staking_contract_Store_$memory, $t0);

    // if ($t4) goto L1 else goto L0 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/staking_contract.move:623:9+87
    if ($t4) { goto L1; } else { goto L0; }

    // label L1 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/staking_contract.move:623:9+87
L1:

    // goto L2 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/staking_contract.move:623:9+87
    assume {:print "$at(2,29637,29724)"} true;
    goto L2;

    // label L0 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/staking_contract.move:623:57+37
L0:

    // $t5 := 3 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/staking_contract.move:623:57+37
    assume {:print "$at(2,29685,29722)"} true;
    $t5 := 3;
    assume $IsValid'u64'($t5);

    // $t6 := error::not_found($t5) on_abort goto L7 with $t7 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/staking_contract.move:623:40+55
    call $t6 := $1_error_not_found($t5);
    if ($abort_flag) {
        assume {:print "$at(2,29668,29723)"} true;
        $t7 := $abort_code;
        assume {:print "$track_abort(56,2):", $t7} $t7 == $t7;
        goto L7;
    }

    // trace_abort($t6) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/staking_contract.move:623:9+87
    assume {:print "$at(2,29637,29724)"} true;
    assume {:print "$track_abort(56,2):", $t6} $t6 == $t6;

    // $t7 := move($t6) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/staking_contract.move:623:9+87
    $t7 := $t6;

    // goto L7 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/staking_contract.move:623:9+87
    goto L7;

    // label L2 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/staking_contract.move:624:63+6
    assume {:print "$at(2,29788,29794)"} true;
L2:

    // $t8 := borrow_global<staking_contract::Store>($t0) on_abort goto L7 with $t7 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/staking_contract.move:624:38+17
    assume {:print "$at(2,29763,29780)"} true;
    if (!$ResourceExists($1_staking_contract_Store_$memory, $t0)) {
        call $ExecFailureAbort();
    } else {
        $t8 := $Mutation($Global($t0), EmptyVec(), $ResourceValue($1_staking_contract_Store_$memory, $t0));
    }
    if ($abort_flag) {
        assume {:print "$at(2,29763,29780)"} true;
        $t7 := $abort_code;
        assume {:print "$track_abort(56,2):", $t7} $t7 == $t7;
        goto L7;
    }

    // $t9 := borrow_field<staking_contract::Store>.staking_contracts($t8) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/staking_contract.move:624:33+55
    $t9 := $ChildMutation($t8, 0, $staking_contracts#$1_staking_contract_Store($Dereference($t8)));

    // $t10 := read_ref($t9) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/staking_contract.move:626:37+30
    assume {:print "$at(2,29868,29898)"} true;
    $t10 := $Dereference($t9);

    // pack_ref_deep($t8) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/staking_contract.move:626:37+30

    // $t11 := simple_map::contains_key<address, staking_contract::StakingContract>($t10, $t1) on_abort goto L7 with $t7 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/staking_contract.move:626:13+54
    call $t11 := $1_simple_map_contains_key'address_$1_staking_contract_StakingContract'($t10, $t1);
    if ($abort_flag) {
        assume {:print "$at(2,29844,29898)"} true;
        $t7 := $abort_code;
        assume {:print "$track_abort(56,2):", $t7} $t7 == $t7;
        goto L7;
    }

    // if ($t11) goto L4 else goto L3 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/staking_contract.move:625:9+157
    assume {:print "$at(2,29823,29980)"} true;
    if ($t11) { goto L4; } else { goto L3; }

    // label L4 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/staking_contract.move:625:9+157
L4:

    // goto L5 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/staking_contract.move:625:9+157
    assume {:print "$at(2,29823,29980)"} true;
    goto L5;

    // label L3 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/staking_contract.move:627:30+39
    assume {:print "$at(2,29929,29968)"} true;
L3:

    // $t12 := 4 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/staking_contract.move:627:30+39
    assume {:print "$at(2,29929,29968)"} true;
    $t12 := 4;
    assume $IsValid'u64'($t12);

    // $t13 := error::not_found($t12) on_abort goto L7 with $t7 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/staking_contract.move:627:13+57
    call $t13 := $1_error_not_found($t12);
    if ($abort_flag) {
        assume {:print "$at(2,29912,29969)"} true;
        $t7 := $abort_code;
        assume {:print "$track_abort(56,2):", $t7} $t7 == $t7;
        goto L7;
    }

    // trace_abort($t13) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/staking_contract.move:625:9+157
    assume {:print "$at(2,29823,29980)"} true;
    assume {:print "$track_abort(56,2):", $t13} $t13 == $t13;

    // $t7 := move($t13) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/staking_contract.move:625:9+157
    $t7 := $t13;

    // goto L7 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/staking_contract.move:625:9+157
    goto L7;

    // label L5 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/staking_contract.move:628:10+1
    assume {:print "$at(2,29980,29981)"} true;
L5:

    // label L6 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/staking_contract.move:629:5+1
    assume {:print "$at(2,29986,29987)"} true;
L6:

    // return () at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/staking_contract.move:629:5+1
    assume {:print "$at(2,29986,29987)"} true;
    return;

    // label L7 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/staking_contract.move:629:5+1
L7:

    // abort($t7) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/staking_contract.move:629:5+1
    assume {:print "$at(2,29986,29987)"} true;
    $abort_code := $t7;
    $abort_flag := true;
    return;

}

// fun staking_contract::get_staking_contract_amounts_internal [baseline] at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/staking_contract.move:653:5+1388
procedure {:inline 1} $1_staking_contract_get_staking_contract_amounts_internal(_$t0: $1_staking_contract_StakingContract) returns ($ret0: int, $ret1: int, $ret2: int)
{
    // declare local variables
    var $t1: int;
    var $t2: int;
    var $t3: int;
    var $t4: int;
    var $t5: int;
    var $t6: $1_stake_StakePool;
    var $t7: int;
    var $t8: int;
    var $t9: int;
    var $t10: int;
    var $t11: int;
    var $t12: int;
    var $t13: int;
    var $t14: int;
    var $t15: int;
    var $t16: int;
    var $t17: int;
    var $t18: int;
    var $t19: int;
    var $t20: int;
    var $t21: int;
    var $t22: int;
    var $t23: int;
    var $t0: $1_staking_contract_StakingContract;
    var $temp_0'$1_staking_contract_StakingContract': $1_staking_contract_StakingContract;
    var $temp_0'u64': int;
    $t0 := _$t0;

    // bytecode translation starts here
    // assume Identical($t5, select staking_contract::StakingContract.pool_address($t0)) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/staking_contract.spec.move:338:9+49
    assume {:print "$at(3,14132,14181)"} true;
    assume ($t5 == $pool_address#$1_staking_contract_StakingContract($t0));

    // assume Identical($t6, global<stake::StakePool>($t5)) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/staking_contract.spec.move:339:9+56
    assume {:print "$at(3,14190,14246)"} true;
    assume ($t6 == $ResourceValue($1_stake_StakePool_$memory, $t5));

    // assume Identical($t7, coin::$value<aptos_coin::AptosCoin>(select stake::StakePool.active($t6))) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/staking_contract.spec.move:340:9+44
    assume {:print "$at(3,14255,14299)"} true;
    assume ($t7 == $1_coin_$value'$1_aptos_coin_AptosCoin'($active#$1_stake_StakePool($t6)));

    // assume Identical($t8, coin::$value<aptos_coin::AptosCoin>(select stake::StakePool.pending_active($t6))) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/staking_contract.spec.move:341:9+60
    assume {:print "$at(3,14308,14368)"} true;
    assume ($t8 == $1_coin_$value'$1_aptos_coin_AptosCoin'($pending_active#$1_stake_StakePool($t6)));

    // assume Identical($t9, Add($t7, $t8)) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/staking_contract.spec.move:342:9+49
    assume {:print "$at(3,14377,14426)"} true;
    assume ($t9 == ($t7 + $t8));

    // assume Identical($t10, Sub($t9, select staking_contract::StakingContract.principal($t0))) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/staking_contract.spec.move:343:9+74
    assume {:print "$at(3,14435,14509)"} true;
    assume ($t10 == ($t9 - $principal#$1_staking_contract_StakingContract($t0)));

    // trace_local[staking_contract]($t0) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/staking_contract.move:653:5+1
    assume {:print "$at(2,31011,31012)"} true;
    assume {:print "$track_local(56,9,0):", $t0} $t0 == $t0;

    // $t11 := get_field<staking_contract::StakingContract>.pool_address($t0) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/staking_contract.move:658:63+29
    assume {:print "$at(2,31532,31561)"} true;
    $t11 := $pool_address#$1_staking_contract_StakingContract($t0);

    // ($t12, $t13, $t14, $t15) := stake::get_stake($t11) on_abort goto L2 with $t16 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/staking_contract.move:658:46+47
    call $t12,$t13,$t14,$t15 := $1_stake_get_stake($t11);
    if ($abort_flag) {
        assume {:print "$at(2,31515,31562)"} true;
        $t16 := $abort_code;
        assume {:print "$track_abort(56,9):", $t16} $t16 == $t16;
        goto L2;
    }

    // destroy($t15) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/staking_contract.move:658:41+1

    // trace_local[pending_active]($t14) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/staking_contract.move:658:25+14
    assume {:print "$track_local(56,9,3):", $t14} $t14 == $t14;

    // destroy($t13) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/staking_contract.move:658:22+1

    // $t17 := +($t12, $t14) on_abort goto L2 with $t16 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/staking_contract.move:659:41+1
    assume {:print "$at(2,31604,31605)"} true;
    call $t17 := $AddU64($t12, $t14);
    if ($abort_flag) {
        assume {:print "$at(2,31604,31605)"} true;
        $t16 := $abort_code;
        assume {:print "$track_abort(56,9):", $t16} $t16 == $t16;
        goto L2;
    }

    // trace_local[total_active_stake]($t17) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/staking_contract.move:659:13+18
    assume {:print "$track_local(56,9,4):", $t17} $t17 == $t17;

    // assume Le(Sub($t17, select staking_contract::StakingContract.principal($t0)), 100) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/staking_contract.move:662:13+62
    assume {:print "$at(2,31716,31778)"} true;
    assume (($t17 - $principal#$1_staking_contract_StakingContract($t0)) <= 100);

    // $t18 := get_field<staking_contract::StakingContract>.principal($t0) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/staking_contract.move:664:56+26
    assume {:print "$at(2,31845,31871)"} true;
    $t18 := $principal#$1_staking_contract_StakingContract($t0);

    // $t19 := -($t17, $t18) on_abort goto L2 with $t16 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/staking_contract.move:664:54+1
    call $t19 := $Sub($t17, $t18);
    if ($abort_flag) {
        assume {:print "$at(2,31843,31844)"} true;
        $t16 := $abort_code;
        assume {:print "$track_abort(56,9):", $t16} $t16 == $t16;
        goto L2;
    }

    // trace_local[accumulated_rewards]($t19) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/staking_contract.move:664:13+19
    assume {:print "$track_local(56,9,1):", $t19} $t19 == $t19;

    // assume And(Ge(select staking_contract::StakingContract.commission_percentage($t0), 0), Le(select staking_contract::StakingContract.commission_percentage($t0), 100)) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/staking_contract.move:668:13+100
    assume {:print "$at(2,32112,32212)"} true;
    assume (($commission_percentage#$1_staking_contract_StakingContract($t0) >= 0) && ($commission_percentage#$1_staking_contract_StakingContract($t0) <= 100));

    // $t20 := get_field<staking_contract::StakingContract>.commission_percentage($t0) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/staking_contract.move:670:55+38
    assume {:print "$at(2,32278,32316)"} true;
    $t20 := $commission_percentage#$1_staking_contract_StakingContract($t0);

    // $t21 := *($t19, $t20) on_abort goto L2 with $t16 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/staking_contract.move:670:53+1
    call $t21 := $MulU64($t19, $t20);
    if ($abort_flag) {
        assume {:print "$at(2,32276,32277)"} true;
        $t16 := $abort_code;
        assume {:print "$track_abort(56,9):", $t16} $t16 == $t16;
        goto L2;
    }

    // $t22 := 100 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/staking_contract.move:670:96+3
    $t22 := 100;
    assume $IsValid'u64'($t22);

    // $t23 := /($t21, $t22) on_abort goto L2 with $t16 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/staking_contract.move:670:94+1
    call $t23 := $Div($t21, $t22);
    if ($abort_flag) {
        assume {:print "$at(2,32317,32318)"} true;
        $t16 := $abort_code;
        assume {:print "$track_abort(56,9):", $t16} $t16 == $t16;
        goto L2;
    }

    // trace_local[commission_amount]($t23) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/staking_contract.move:670:13+17
    assume {:print "$track_local(56,9,2):", $t23} $t23 == $t23;

    // trace_return[0]($t17) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/staking_contract.move:672:9+60
    assume {:print "$at(2,32333,32393)"} true;
    assume {:print "$track_return(56,9,0):", $t17} $t17 == $t17;

    // trace_return[1]($t19) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/staking_contract.move:672:9+60
    assume {:print "$track_return(56,9,1):", $t19} $t19 == $t19;

    // trace_return[2]($t23) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/staking_contract.move:672:9+60
    assume {:print "$track_return(56,9,2):", $t23} $t23 == $t23;

    // label L1 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/staking_contract.move:673:5+1
    assume {:print "$at(2,32398,32399)"} true;
L1:

    // return ($t17, $t19, $t23) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/staking_contract.move:673:5+1
    assume {:print "$at(2,32398,32399)"} true;
    $ret0 := $t17;
    $ret1 := $t19;
    $ret2 := $t23;
    return;

    // label L2 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/staking_contract.move:673:5+1
L2:

    // abort($t16) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/staking_contract.move:673:5+1
    assume {:print "$at(2,32398,32399)"} true;
    $abort_code := $t16;
    $abort_flag := true;
    return;

}

// fun staking_contract::staking_contract_amounts [verification] at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/staking_contract.move:208:5+395
procedure {:timeLimit 200} $1_staking_contract_staking_contract_amounts$verify(_$t0: int, _$t1: int) returns ($ret0: int, $ret1: int, $ret2: int)
{
    // declare local variables
    var $t2: Table int ($1_staking_contract_StakingContract);
    var $t3: $1_staking_contract_StakingContract;
    var $t4: int;
    var $t5: $1_stake_StakePool;
    var $t6: int;
    var $t7: int;
    var $t8: int;
    var $t9: int;
    var $t10: Table int ($1_staking_contract_StakingContract);
    var $t11: int;
    var $t12: $1_stake_StakePool;
    var $t13: int;
    var $t14: int;
    var $t15: int;
    var $t16: int;
    var $t17: Table int ($1_staking_contract_StakingContract);
    var $t18: int;
    var $t19: $1_staking_contract_Store;
    var $t20: Table int ($1_staking_contract_StakingContract);
    var $t21: $1_staking_contract_StakingContract;
    var $t22: int;
    var $t23: $1_stake_StakePool;
    var $t24: int;
    var $t25: int;
    var $t26: int;
    var $t27: int;
    var $t28: int;
    var $t29: int;
    var $t30: int;
    var $t0: int;
    var $t1: int;
    var $temp_0'address': int;
    var $temp_0'u64': int;
    var $1_staking_contract_Store_$memory#20: $Memory $1_staking_contract_Store;
    var $1_stake_StakePool_$memory#21: $Memory $1_stake_StakePool;
    $t0 := _$t0;
    $t1 := _$t1;

    // verification entrypoint assumptions
    call $InitVerification();

    // bytecode translation starts here
    // assume WellFormed($t0) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/staking_contract.move:208:5+1
    assume {:print "$at(2,9573,9574)"} true;
    assume $IsValid'address'($t0);

    // assume WellFormed($t1) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/staking_contract.move:208:5+1
    assume $IsValid'address'($t1);

    // assume forall $rsc: ResourceDomain<coin::CoinInfo<aptos_coin::AptosCoin>>(): And(WellFormed($rsc), And(Le(Len<optional_aggregator::OptionalAggregator>(select option::Option.vec(select coin::CoinInfo.supply($rsc))), 1), forall $elem: select option::Option.vec(select coin::CoinInfo.supply($rsc)): And(And(And(And(And(Iff(option::$is_some<aggregator::Aggregator>(select optional_aggregator::OptionalAggregator.aggregator($elem)), option::$is_none<optional_aggregator::Integer>(select optional_aggregator::OptionalAggregator.integer($elem))), Iff(option::$is_some<optional_aggregator::Integer>(select optional_aggregator::OptionalAggregator.integer($elem)), option::$is_none<aggregator::Aggregator>(select optional_aggregator::OptionalAggregator.aggregator($elem)))), Implies(option::$is_some<optional_aggregator::Integer>(select optional_aggregator::OptionalAggregator.integer($elem)), Le(select optional_aggregator::Integer.value(option::$borrow<optional_aggregator::Integer>(select optional_aggregator::OptionalAggregator.integer($elem))), select optional_aggregator::Integer.limit(option::$borrow<optional_aggregator::Integer>(select optional_aggregator::OptionalAggregator.integer($elem)))))), Implies(option::$is_some<aggregator::Aggregator>(select optional_aggregator::OptionalAggregator.aggregator($elem)), Le(aggregator::spec_aggregator_get_val(option::$borrow<aggregator::Aggregator>(select optional_aggregator::OptionalAggregator.aggregator($elem))), aggregator::spec_get_limit(option::$borrow<aggregator::Aggregator>(select optional_aggregator::OptionalAggregator.aggregator($elem)))))), Le(Len<aggregator::Aggregator>(select option::Option.vec(select optional_aggregator::OptionalAggregator.aggregator($elem))), 1)), Le(Len<optional_aggregator::Integer>(select option::Option.vec(select optional_aggregator::OptionalAggregator.integer($elem))), 1)))) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/staking_contract.move:208:5+1
    assume (forall $a_0: int :: {$ResourceValue($1_coin_CoinInfo'$1_aptos_coin_AptosCoin'_$memory, $a_0)}(var $rsc := $ResourceValue($1_coin_CoinInfo'$1_aptos_coin_AptosCoin'_$memory, $a_0);
    (($IsValid'$1_coin_CoinInfo'$1_aptos_coin_AptosCoin''($rsc) && ((LenVec($vec#$1_option_Option'$1_optional_aggregator_OptionalAggregator'($supply#$1_coin_CoinInfo'$1_aptos_coin_AptosCoin'($rsc))) <= 1) && (var $range_1 := $vec#$1_option_Option'$1_optional_aggregator_OptionalAggregator'($supply#$1_coin_CoinInfo'$1_aptos_coin_AptosCoin'($rsc)); (forall $i_2: int :: InRangeVec($range_1, $i_2) ==> (var $elem := ReadVec($range_1, $i_2);
    ((((((($1_option_$is_some'$1_aggregator_Aggregator'($aggregator#$1_optional_aggregator_OptionalAggregator($elem)) <==> $1_option_$is_none'$1_optional_aggregator_Integer'($integer#$1_optional_aggregator_OptionalAggregator($elem))) && ($1_option_$is_some'$1_optional_aggregator_Integer'($integer#$1_optional_aggregator_OptionalAggregator($elem)) <==> $1_option_$is_none'$1_aggregator_Aggregator'($aggregator#$1_optional_aggregator_OptionalAggregator($elem)))) && ($1_option_$is_some'$1_optional_aggregator_Integer'($integer#$1_optional_aggregator_OptionalAggregator($elem)) ==> ($value#$1_optional_aggregator_Integer($1_option_$borrow'$1_optional_aggregator_Integer'($integer#$1_optional_aggregator_OptionalAggregator($elem))) <= $limit#$1_optional_aggregator_Integer($1_option_$borrow'$1_optional_aggregator_Integer'($integer#$1_optional_aggregator_OptionalAggregator($elem)))))) && ($1_option_$is_some'$1_aggregator_Aggregator'($aggregator#$1_optional_aggregator_OptionalAggregator($elem)) ==> ($1_aggregator_spec_aggregator_get_val($1_option_$borrow'$1_aggregator_Aggregator'($aggregator#$1_optional_aggregator_OptionalAggregator($elem))) <= $1_aggregator_spec_get_limit($1_option_$borrow'$1_aggregator_Aggregator'($aggregator#$1_optional_aggregator_OptionalAggregator($elem)))))) && (LenVec($vec#$1_option_Option'$1_aggregator_Aggregator'($aggregator#$1_optional_aggregator_OptionalAggregator($elem))) <= 1)) && (LenVec($vec#$1_option_Option'$1_optional_aggregator_Integer'($integer#$1_optional_aggregator_OptionalAggregator($elem))) <= 1)))))))))));

    // assume forall $rsc: ResourceDomain<coin::Ghost$supply<aptos_coin::AptosCoin>>(): WellFormed($rsc) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/staking_contract.move:208:5+1
    assume (forall $a_0: int :: {$ResourceValue($1_coin_Ghost$supply'$1_aptos_coin_AptosCoin'_$memory, $a_0)}(var $rsc := $ResourceValue($1_coin_Ghost$supply'$1_aptos_coin_AptosCoin'_$memory, $a_0);
    ($IsValid'$1_coin_Ghost$supply'$1_aptos_coin_AptosCoin''($rsc))));

    // assume exists<coin::Ghost$supply<aptos_coin::AptosCoin>>(0) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/staking_contract.move:208:5+1
    assume $ResourceExists($1_coin_Ghost$supply'$1_aptos_coin_AptosCoin'_$memory, 0);

    // assume forall $rsc: ResourceDomain<coin::Ghost$aggregate_supply<aptos_coin::AptosCoin>>(): WellFormed($rsc) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/staking_contract.move:208:5+1
    assume (forall $a_0: int :: {$ResourceValue($1_coin_Ghost$aggregate_supply'$1_aptos_coin_AptosCoin'_$memory, $a_0)}(var $rsc := $ResourceValue($1_coin_Ghost$aggregate_supply'$1_aptos_coin_AptosCoin'_$memory, $a_0);
    ($IsValid'$1_coin_Ghost$aggregate_supply'$1_aptos_coin_AptosCoin''($rsc))));

    // assume exists<coin::Ghost$aggregate_supply<aptos_coin::AptosCoin>>(0) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/staking_contract.move:208:5+1
    assume $ResourceExists($1_coin_Ghost$aggregate_supply'$1_aptos_coin_AptosCoin'_$memory, 0);

    // assume forall $rsc: ResourceDomain<stake::StakePool>(): WellFormed($rsc) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/staking_contract.move:208:5+1
    assume (forall $a_0: int :: {$ResourceValue($1_stake_StakePool_$memory, $a_0)}(var $rsc := $ResourceValue($1_stake_StakePool_$memory, $a_0);
    ($IsValid'$1_stake_StakePool'($rsc))));

    // assume forall $rsc: ResourceDomain<stake::ValidatorConfig>(): WellFormed($rsc) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/staking_contract.move:208:5+1
    assume (forall $a_0: int :: {$ResourceValue($1_stake_ValidatorConfig_$memory, $a_0)}(var $rsc := $ResourceValue($1_stake_ValidatorConfig_$memory, $a_0);
    ($IsValid'$1_stake_ValidatorConfig'($rsc))));

    // assume forall $rsc: ResourceDomain<stake::ValidatorPerformance>(): WellFormed($rsc) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/staking_contract.move:208:5+1
    assume (forall $a_0: int :: {$ResourceValue($1_stake_ValidatorPerformance_$memory, $a_0)}(var $rsc := $ResourceValue($1_stake_ValidatorPerformance_$memory, $a_0);
    ($IsValid'$1_stake_ValidatorPerformance'($rsc))));

    // assume forall $rsc: ResourceDomain<stake::ValidatorSet>(): WellFormed($rsc) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/staking_contract.move:208:5+1
    assume (forall $a_0: int :: {$ResourceValue($1_stake_ValidatorSet_$memory, $a_0)}(var $rsc := $ResourceValue($1_stake_ValidatorSet_$memory, $a_0);
    ($IsValid'$1_stake_ValidatorSet'($rsc))));

    // assume forall $rsc: ResourceDomain<staking_contract::Store>(): And(WellFormed($rsc), forall $key: select staking_contract::Store.staking_contracts($rsc): And(forall addr: TypeDomain<address>(): Eq<bool>(simple_map::spec_contains_key<address, u64>(select pool_u64::Pool.shares(select staking_contract::StakingContract.distribution_pool(simple_map::spec_get<address, staking_contract::StakingContract>(select staking_contract::Store.staking_contracts($rsc), $key))), addr), vector::spec_contains<address>(select pool_u64::Pool.shareholders(select staking_contract::StakingContract.distribution_pool(simple_map::spec_get<address, staking_contract::StakingContract>(select staking_contract::Store.staking_contracts($rsc), $key))), addr)), forall i: Range(0, Len<address>(select pool_u64::Pool.shareholders(select staking_contract::StakingContract.distribution_pool(simple_map::spec_get<address, staking_contract::StakingContract>(select staking_contract::Store.staking_contracts($rsc), $key))))), j: Range(0, Len<address>(select pool_u64::Pool.shareholders(select staking_contract::StakingContract.distribution_pool(simple_map::spec_get<address, staking_contract::StakingContract>(select staking_contract::Store.staking_contracts($rsc), $key))))): Implies(Eq<address>(Index(select pool_u64::Pool.shareholders(select staking_contract::StakingContract.distribution_pool(simple_map::spec_get<address, staking_contract::StakingContract>(select staking_contract::Store.staking_contracts($rsc), $key))), i), Index(select pool_u64::Pool.shareholders(select staking_contract::StakingContract.distribution_pool(simple_map::spec_get<address, staking_contract::StakingContract>(select staking_contract::Store.staking_contracts($rsc), $key))), j)), Eq<num>(i, j)))) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/staking_contract.move:208:5+1
    assume (forall $a_0: int :: {$ResourceValue($1_staking_contract_Store_$memory, $a_0)}(var $rsc := $ResourceValue($1_staking_contract_Store_$memory, $a_0);
    (($IsValid'$1_staking_contract_Store'($rsc) && (var $range_1 := $staking_contracts#$1_staking_contract_Store($rsc); (forall $key: int :: ContainsTable($range_1, $EncodeKey'address'($key)) ==> (((forall addr: int :: $IsValid'address'(addr) ==> ($IsEqual'bool'($1_simple_map_spec_contains_key'address_u64'($shares#$1_pool_u64_Pool($distribution_pool#$1_staking_contract_StakingContract($1_simple_map_spec_get'address_$1_staking_contract_StakingContract'($staking_contracts#$1_staking_contract_Store($rsc), $key))), addr), $1_vector_spec_contains'address'($shareholders#$1_pool_u64_Pool($distribution_pool#$1_staking_contract_StakingContract($1_simple_map_spec_get'address_$1_staking_contract_StakingContract'($staking_contracts#$1_staking_contract_Store($rsc), $key))), addr)))) && (var $range_2 := $Range(0, LenVec($shareholders#$1_pool_u64_Pool($distribution_pool#$1_staking_contract_StakingContract($1_simple_map_spec_get'address_$1_staking_contract_StakingContract'($staking_contracts#$1_staking_contract_Store($rsc), $key))))); (var $range_3 := $Range(0, LenVec($shareholders#$1_pool_u64_Pool($distribution_pool#$1_staking_contract_StakingContract($1_simple_map_spec_get'address_$1_staking_contract_StakingContract'($staking_contracts#$1_staking_contract_Store($rsc), $key))))); (forall $i_4: int, $i_5: int :: $InRange($range_2, $i_4) ==> $InRange($range_3, $i_5) ==> (var i := $i_4;
    (var j := $i_5;
    (($IsEqual'address'(ReadVec($shareholders#$1_pool_u64_Pool($distribution_pool#$1_staking_contract_StakingContract($1_simple_map_spec_get'address_$1_staking_contract_StakingContract'($staking_contracts#$1_staking_contract_Store($rsc), $key))), i), ReadVec($shareholders#$1_pool_u64_Pool($distribution_pool#$1_staking_contract_StakingContract($1_simple_map_spec_get'address_$1_staking_contract_StakingContract'($staking_contracts#$1_staking_contract_Store($rsc), $key))), j)) ==> $IsEqual'num'(i, j))))))))))))))));

    // assume Implies(exists<stake::ValidatorSet>(1), stake::validator_set_is_valid()) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/staking_contract.move:208:5+395
    // global invariant at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/stake.spec.move:9:9+92
    assume ($ResourceExists($1_stake_ValidatorSet_$memory, 1) ==> $1_stake_validator_set_is_valid($1_stake_StakePool_$memory, $1_stake_ValidatorConfig_$memory, $1_stake_ValidatorPerformance_$memory, $1_stake_ValidatorSet_$memory));

    // assume Identical($t2, select staking_contract::Store.staking_contracts(global<staking_contract::Store>($t0))) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/staking_contract.spec.move:25:9+64
    assume {:print "$at(3,914,978)"} true;
    assume ($t2 == $staking_contracts#$1_staking_contract_Store($ResourceValue($1_staking_contract_Store_$memory, $t0)));

    // assume Identical($t3, simple_map::spec_get<address, staking_contract::StakingContract>($t2, $t1)) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/staking_contract.spec.move:26:9+73
    assume {:print "$at(3,987,1060)"} true;
    assume ($t3 == $1_simple_map_spec_get'address_$1_staking_contract_StakingContract'($t2, $t1));

    // assume Identical($t4, select staking_contract::StakingContract.pool_address($t3)) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/staking_contract.spec.move:30:9+49
    assume {:print "$at(3,1179,1228)"} true;
    assume ($t4 == $pool_address#$1_staking_contract_StakingContract($t3));

    // assume Identical($t5, global<stake::StakePool>($t4)) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/staking_contract.spec.move:31:9+56
    assume {:print "$at(3,1237,1293)"} true;
    assume ($t5 == $ResourceValue($1_stake_StakePool_$memory, $t4));

    // assume Identical($t6, coin::$value<aptos_coin::AptosCoin>(select stake::StakePool.active($t5))) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/staking_contract.spec.move:32:9+44
    assume {:print "$at(3,1302,1346)"} true;
    assume ($t6 == $1_coin_$value'$1_aptos_coin_AptosCoin'($active#$1_stake_StakePool($t5)));

    // assume Identical($t7, coin::$value<aptos_coin::AptosCoin>(select stake::StakePool.pending_active($t5))) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/staking_contract.spec.move:33:9+60
    assume {:print "$at(3,1355,1415)"} true;
    assume ($t7 == $1_coin_$value'$1_aptos_coin_AptosCoin'($pending_active#$1_stake_StakePool($t5)));

    // assume Identical($t8, Add($t6, $t7)) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/staking_contract.spec.move:34:9+49
    assume {:print "$at(3,1424,1473)"} true;
    assume ($t8 == ($t6 + $t7));

    // assume Identical($t9, Sub($t8, select staking_contract::StakingContract.principal($t3))) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/staking_contract.spec.move:35:9+74
    assume {:print "$at(3,1482,1556)"} true;
    assume ($t9 == ($t8 - $principal#$1_staking_contract_StakingContract($t3)));

    // assume Identical($t10, select staking_contract::Store.staking_contracts(global<staking_contract::Store>($t0))) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/staking_contract.spec.move:307:9+64
    assume {:print "$at(3,12992,13056)"} true;
    assume ($t10 == $staking_contracts#$1_staking_contract_Store($ResourceValue($1_staking_contract_Store_$memory, $t0)));

    // assume Identical($t11, select staking_contract::StakingContract.pool_address($t3)) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/staking_contract.spec.move:338:9+49
    assume {:print "$at(3,14132,14181)"} true;
    assume ($t11 == $pool_address#$1_staking_contract_StakingContract($t3));

    // assume Identical($t12, global<stake::StakePool>($t11)) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/staking_contract.spec.move:339:9+56
    assume {:print "$at(3,14190,14246)"} true;
    assume ($t12 == $ResourceValue($1_stake_StakePool_$memory, $t11));

    // assume Identical($t13, coin::$value<aptos_coin::AptosCoin>(select stake::StakePool.active($t12))) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/staking_contract.spec.move:340:9+44
    assume {:print "$at(3,14255,14299)"} true;
    assume ($t13 == $1_coin_$value'$1_aptos_coin_AptosCoin'($active#$1_stake_StakePool($t12)));

    // assume Identical($t14, coin::$value<aptos_coin::AptosCoin>(select stake::StakePool.pending_active($t12))) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/staking_contract.spec.move:341:9+60
    assume {:print "$at(3,14308,14368)"} true;
    assume ($t14 == $1_coin_$value'$1_aptos_coin_AptosCoin'($pending_active#$1_stake_StakePool($t12)));

    // assume Identical($t15, Add($t13, $t14)) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/staking_contract.spec.move:342:9+49
    assume {:print "$at(3,14377,14426)"} true;
    assume ($t15 == ($t13 + $t14));

    // assume Identical($t16, Sub($t15, select staking_contract::StakingContract.principal($t3))) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/staking_contract.spec.move:343:9+74
    assume {:print "$at(3,14435,14509)"} true;
    assume ($t16 == ($t15 - $principal#$1_staking_contract_StakingContract($t3)));

    // assume And(Ge(select staking_contract::StakingContract.commission_percentage($t3), 0), Le(select staking_contract::StakingContract.commission_percentage($t3), 100)) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/staking_contract.spec.move:24:9+102
    assume {:print "$at(3,803,905)"} true;
    assume (($commission_percentage#$1_staking_contract_StakingContract($t3) >= 0) && ($commission_percentage#$1_staking_contract_StakingContract($t3) <= 100));

    // @21 := save_mem(stake::StakePool) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/staking_contract.spec.move:24:9+102
    $1_stake_StakePool_$memory#21 := $1_stake_StakePool_$memory;

    // @20 := save_mem(staking_contract::Store) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/staking_contract.spec.move:24:9+102
    $1_staking_contract_Store_$memory#20 := $1_staking_contract_Store_$memory;

    // trace_local[staker]($t0) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/staking_contract.move:208:5+1
    assume {:print "$at(2,9573,9574)"} true;
    assume {:print "$track_local(56,17,0):", $t0} $t0 == $t0;

    // trace_local[operator]($t1) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/staking_contract.move:208:5+1
    assume {:print "$track_local(56,17,1):", $t1} $t1 == $t1;

    // assume Identical($t17, select staking_contract::Store.staking_contracts(global<staking_contract::Store>($t0))) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/staking_contract.spec.move:307:9+64
    assume {:print "$at(3,12992,13056)"} true;
    assume ($t17 == $staking_contracts#$1_staking_contract_Store($ResourceValue($1_staking_contract_Store_$memory, $t0)));

    // staking_contract::assert_staking_contract_exists($t0, $t1) on_abort goto L2 with $t18 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/staking_contract.move:209:9+48
    assume {:print "$at(2,9687,9735)"} true;
    call $1_staking_contract_assert_staking_contract_exists($t0, $t1);
    if ($abort_flag) {
        assume {:print "$at(2,9687,9735)"} true;
        $t18 := $abort_code;
        assume {:print "$track_abort(56,17):", $t18} $t18 == $t18;
        goto L2;
    }

    // $t19 := get_global<staking_contract::Store>($t0) on_abort goto L2 with $t18 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/staking_contract.move:210:34+13
    assume {:print "$at(2,9770,9783)"} true;
    if (!$ResourceExists($1_staking_contract_Store_$memory, $t0)) {
        call $ExecFailureAbort();
    } else {
        $t19 := $ResourceValue($1_staking_contract_Store_$memory, $t0);
    }
    if ($abort_flag) {
        assume {:print "$at(2,9770,9783)"} true;
        $t18 := $abort_code;
        assume {:print "$track_abort(56,17):", $t18} $t18 == $t18;
        goto L2;
    }

    // $t20 := get_field<staking_contract::Store>.staking_contracts($t19) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/staking_contract.move:210:33+47
    $t20 := $staking_contracts#$1_staking_contract_Store($t19);

    // $t21 := simple_map::borrow<address, staking_contract::StakingContract>($t20, $t1) on_abort goto L2 with $t18 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/staking_contract.move:211:32+48
    assume {:print "$at(2,9849,9897)"} true;
    call $t21 := $1_simple_map_borrow'address_$1_staking_contract_StakingContract'($t20, $t1);
    if ($abort_flag) {
        assume {:print "$at(2,9849,9897)"} true;
        $t18 := $abort_code;
        assume {:print "$track_abort(56,17):", $t18} $t18 == $t18;
        goto L2;
    }

    // assume Identical($t22, select staking_contract::StakingContract.pool_address($t21)) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/staking_contract.spec.move:338:9+49
    assume {:print "$at(3,14132,14181)"} true;
    assume ($t22 == $pool_address#$1_staking_contract_StakingContract($t21));

    // assume Identical($t23, global<stake::StakePool>($t22)) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/staking_contract.spec.move:339:9+56
    assume {:print "$at(3,14190,14246)"} true;
    assume ($t23 == $ResourceValue($1_stake_StakePool_$memory, $t22));

    // assume Identical($t24, coin::$value<aptos_coin::AptosCoin>(select stake::StakePool.active($t23))) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/staking_contract.spec.move:340:9+44
    assume {:print "$at(3,14255,14299)"} true;
    assume ($t24 == $1_coin_$value'$1_aptos_coin_AptosCoin'($active#$1_stake_StakePool($t23)));

    // assume Identical($t25, coin::$value<aptos_coin::AptosCoin>(select stake::StakePool.pending_active($t23))) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/staking_contract.spec.move:341:9+60
    assume {:print "$at(3,14308,14368)"} true;
    assume ($t25 == $1_coin_$value'$1_aptos_coin_AptosCoin'($pending_active#$1_stake_StakePool($t23)));

    // assume Identical($t26, Add($t24, $t25)) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/staking_contract.spec.move:342:9+49
    assume {:print "$at(3,14377,14426)"} true;
    assume ($t26 == ($t24 + $t25));

    // assume Identical($t27, Sub($t26, select staking_contract::StakingContract.principal($t21))) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/staking_contract.spec.move:343:9+74
    assume {:print "$at(3,14435,14509)"} true;
    assume ($t27 == ($t26 - $principal#$1_staking_contract_StakingContract($t21)));

    // ($t28, $t29, $t30) := staking_contract::get_staking_contract_amounts_internal($t21) on_abort goto L2 with $t18 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/staking_contract.move:212:9+55
    assume {:print "$at(2,9907,9962)"} true;
    call $t28,$t29,$t30 := $1_staking_contract_get_staking_contract_amounts_internal($t21);
    if ($abort_flag) {
        assume {:print "$at(2,9907,9962)"} true;
        $t18 := $abort_code;
        assume {:print "$track_abort(56,17):", $t18} $t18 == $t18;
        goto L2;
    }

    // trace_return[0]($t28) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/staking_contract.move:212:9+55
    assume {:print "$track_return(56,17,0):", $t28} $t28 == $t28;

    // trace_return[1]($t29) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/staking_contract.move:212:9+55
    assume {:print "$track_return(56,17,1):", $t29} $t29 == $t29;

    // trace_return[2]($t30) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/staking_contract.move:212:9+55
    assume {:print "$track_return(56,17,2):", $t30} $t30 == $t30;

    // label L1 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/staking_contract.move:213:5+1
    assume {:print "$at(2,9967,9968)"} true;
L1:

    // assert Not(Not(exists[@20]<staking_contract::Store>($t0))) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/staking_contract.spec.move:306:9+33
    assume {:print "$at(3,12950,12983)"} true;
    assert {:msg "assert_failed(3,12950,12983): function does not abort under this condition"}
      !!$ResourceExists($1_staking_contract_Store_$memory#20, $t0);

    // assert Not(Not(simple_map::spec_contains_key[]<address, staking_contract::StakingContract>($t10, $t1))) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/staking_contract.spec.move:308:9+70
    assume {:print "$at(3,13065,13135)"} true;
    assert {:msg "assert_failed(3,13065,13135): function does not abort under this condition"}
      !!$1_simple_map_spec_contains_key'address_$1_staking_contract_StakingContract'($t10, $t1);

    // assert Not(Not(exists[@21]<stake::StakePool>($t11))) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/staking_contract.spec.move:344:9+50
    assume {:print "$at(3,14518,14568)"} true;
    assert {:msg "assert_failed(3,14518,14568): function does not abort under this condition"}
      !!$ResourceExists($1_stake_StakePool_$memory#21, $t11);

    // assert Not(Gt(Add($t13, $t14), 18446744073709551615)) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/staking_contract.spec.move:345:9+44
    assume {:print "$at(3,14577,14621)"} true;
    assert {:msg "assert_failed(3,14577,14621): function does not abort under this condition"}
      !(($t13 + $t14) > 18446744073709551615);

    // assert Not(Lt($t15, select staking_contract::StakingContract.principal($t3))) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/staking_contract.spec.move:346:9+58
    assume {:print "$at(3,14630,14688)"} true;
    assert {:msg "assert_failed(3,14630,14688): function does not abort under this condition"}
      !($t15 < $principal#$1_staking_contract_StakingContract($t3));

    // assert Not(Gt(Mul($t16, select staking_contract::StakingContract.commission_percentage($t3)), 18446744073709551615)) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/staking_contract.spec.move:347:9+81
    assume {:print "$at(3,14697,14778)"} true;
    assert {:msg "assert_failed(3,14697,14778): function does not abort under this condition"}
      !(($t16 * $commission_percentage#$1_staking_contract_StakingContract($t3)) > 18446744073709551615);

    // assert Eq<u64>($t28, $t8) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/staking_contract.spec.move:36:9+39
    assume {:print "$at(3,1565,1604)"} true;
    assert {:msg "assert_failed(3,1565,1604): post-condition does not hold"}
      $IsEqual'u64'($t28, $t8);

    // assert Eq<u64>($t29, $t9) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/staking_contract.spec.move:37:9+40
    assume {:print "$at(3,1613,1653)"} true;
    assert {:msg "assert_failed(3,1613,1653): post-condition does not hold"}
      $IsEqual'u64'($t29, $t9);

    // assert Eq<u64>($t30, Div(Mul($t9, select staking_contract::StakingContract.commission_percentage($t3)), 100)) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/staking_contract.spec.move:38:9+87
    assume {:print "$at(3,1662,1749)"} true;
    assert {:msg "assert_failed(3,1662,1749): post-condition does not hold"}
      $IsEqual'u64'($t30, (($t9 * $commission_percentage#$1_staking_contract_StakingContract($t3)) div 100));

    // return ($t28, $t29, $t30) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/staking_contract.spec.move:38:9+87
    $ret0 := $t28;
    $ret1 := $t29;
    $ret2 := $t30;
    return;

    // label L2 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/staking_contract.move:213:5+1
    assume {:print "$at(2,9967,9968)"} true;
L2:

    // assert Or(Or(Or(Or(Or(Not(exists[@20]<staking_contract::Store>($t0)), Not(simple_map::spec_contains_key[]<address, staking_contract::StakingContract>($t10, $t1))), Not(exists[@21]<stake::StakePool>($t11))), Gt(Add($t13, $t14), 18446744073709551615)), Lt($t15, select staking_contract::StakingContract.principal($t3))), Gt(Mul($t16, select staking_contract::StakingContract.commission_percentage($t3)), 18446744073709551615)) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/staking_contract.spec.move:22:5+1075
    assume {:print "$at(3,680,1755)"} true;
    assert {:msg "assert_failed(3,680,1755): abort not covered by any of the `aborts_if` clauses"}
      (((((!$ResourceExists($1_staking_contract_Store_$memory#20, $t0) || !$1_simple_map_spec_contains_key'address_$1_staking_contract_StakingContract'($t10, $t1)) || !$ResourceExists($1_stake_StakePool_$memory#21, $t11)) || (($t13 + $t14) > 18446744073709551615)) || ($t15 < $principal#$1_staking_contract_StakingContract($t3))) || (($t16 * $commission_percentage#$1_staking_contract_StakingContract($t3)) > 18446744073709551615));

    // abort($t18) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/staking_contract.spec.move:22:5+1075
    $abort_code := $t18;
    $abort_flag := true;
    return;

}
