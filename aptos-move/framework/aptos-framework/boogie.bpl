
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
// Native Vector implementation for element type `$1_aptos_coin_AptosCoin`

// Not inlined. It appears faster this way.
function $IsEqual'vec'$1_aptos_coin_AptosCoin''(v1: Vec ($1_aptos_coin_AptosCoin), v2: Vec ($1_aptos_coin_AptosCoin)): bool {
    LenVec(v1) == LenVec(v2) &&
    (forall i: int:: InRangeVec(v1, i) ==> $IsEqual'$1_aptos_coin_AptosCoin'(ReadVec(v1, i), ReadVec(v2, i)))
}

// Not inlined.
function $IsPrefix'vec'$1_aptos_coin_AptosCoin''(v: Vec ($1_aptos_coin_AptosCoin), prefix: Vec ($1_aptos_coin_AptosCoin)): bool {
    LenVec(v) >= LenVec(prefix) &&
    (forall i: int:: InRangeVec(prefix, i) ==> $IsEqual'$1_aptos_coin_AptosCoin'(ReadVec(v, i), ReadVec(prefix, i)))
}

// Not inlined.
function $IsSuffix'vec'$1_aptos_coin_AptosCoin''(v: Vec ($1_aptos_coin_AptosCoin), suffix: Vec ($1_aptos_coin_AptosCoin)): bool {
    LenVec(v) >= LenVec(suffix) &&
    (forall i: int:: InRangeVec(suffix, i) ==> $IsEqual'$1_aptos_coin_AptosCoin'(ReadVec(v, LenVec(v) - LenVec(suffix) + i), ReadVec(suffix, i)))
}

// Not inlined.
function $IsValid'vec'$1_aptos_coin_AptosCoin''(v: Vec ($1_aptos_coin_AptosCoin)): bool {
    $IsValid'u64'(LenVec(v)) &&
    (forall i: int:: InRangeVec(v, i) ==> $IsValid'$1_aptos_coin_AptosCoin'(ReadVec(v, i)))
}


function {:inline} $ContainsVec'$1_aptos_coin_AptosCoin'(v: Vec ($1_aptos_coin_AptosCoin), e: $1_aptos_coin_AptosCoin): bool {
    (exists i: int :: $IsValid'u64'(i) && InRangeVec(v, i) && $IsEqual'$1_aptos_coin_AptosCoin'(ReadVec(v, i), e))
}

function $IndexOfVec'$1_aptos_coin_AptosCoin'(v: Vec ($1_aptos_coin_AptosCoin), e: $1_aptos_coin_AptosCoin): int;
axiom (forall v: Vec ($1_aptos_coin_AptosCoin), e: $1_aptos_coin_AptosCoin:: {$IndexOfVec'$1_aptos_coin_AptosCoin'(v, e)}
    (var i := $IndexOfVec'$1_aptos_coin_AptosCoin'(v, e);
     if (!$ContainsVec'$1_aptos_coin_AptosCoin'(v, e)) then i == -1
     else $IsValid'u64'(i) && InRangeVec(v, i) && $IsEqual'$1_aptos_coin_AptosCoin'(ReadVec(v, i), e) &&
        (forall j: int :: $IsValid'u64'(j) && j >= 0 && j < i ==> !$IsEqual'$1_aptos_coin_AptosCoin'(ReadVec(v, j), e))));


function {:inline} $RangeVec'$1_aptos_coin_AptosCoin'(v: Vec ($1_aptos_coin_AptosCoin)): $Range {
    $Range(0, LenVec(v))
}


function {:inline} $EmptyVec'$1_aptos_coin_AptosCoin'(): Vec ($1_aptos_coin_AptosCoin) {
    EmptyVec()
}

procedure {:inline 1} $1_vector_empty'$1_aptos_coin_AptosCoin'() returns (v: Vec ($1_aptos_coin_AptosCoin)) {
    v := EmptyVec();
}

function {:inline} $1_vector_$empty'$1_aptos_coin_AptosCoin'(): Vec ($1_aptos_coin_AptosCoin) {
    EmptyVec()
}

procedure {:inline 1} $1_vector_is_empty'$1_aptos_coin_AptosCoin'(v: Vec ($1_aptos_coin_AptosCoin)) returns (b: bool) {
    b := IsEmptyVec(v);
}

procedure {:inline 1} $1_vector_push_back'$1_aptos_coin_AptosCoin'(m: $Mutation (Vec ($1_aptos_coin_AptosCoin)), val: $1_aptos_coin_AptosCoin) returns (m': $Mutation (Vec ($1_aptos_coin_AptosCoin))) {
    m' := $UpdateMutation(m, ExtendVec($Dereference(m), val));
}

function {:inline} $1_vector_$push_back'$1_aptos_coin_AptosCoin'(v: Vec ($1_aptos_coin_AptosCoin), val: $1_aptos_coin_AptosCoin): Vec ($1_aptos_coin_AptosCoin) {
    ExtendVec(v, val)
}

procedure {:inline 1} $1_vector_pop_back'$1_aptos_coin_AptosCoin'(m: $Mutation (Vec ($1_aptos_coin_AptosCoin))) returns (e: $1_aptos_coin_AptosCoin, m': $Mutation (Vec ($1_aptos_coin_AptosCoin))) {
    var v: Vec ($1_aptos_coin_AptosCoin);
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

procedure {:inline 1} $1_vector_append'$1_aptos_coin_AptosCoin'(m: $Mutation (Vec ($1_aptos_coin_AptosCoin)), other: Vec ($1_aptos_coin_AptosCoin)) returns (m': $Mutation (Vec ($1_aptos_coin_AptosCoin))) {
    m' := $UpdateMutation(m, ConcatVec($Dereference(m), other));
}

procedure {:inline 1} $1_vector_reverse'$1_aptos_coin_AptosCoin'(m: $Mutation (Vec ($1_aptos_coin_AptosCoin))) returns (m': $Mutation (Vec ($1_aptos_coin_AptosCoin))) {
    m' := $UpdateMutation(m, ReverseVec($Dereference(m)));
}

procedure {:inline 1} $1_vector_reverse_append'$1_aptos_coin_AptosCoin'(m: $Mutation (Vec ($1_aptos_coin_AptosCoin)), other: Vec ($1_aptos_coin_AptosCoin)) returns (m': $Mutation (Vec ($1_aptos_coin_AptosCoin))) {
    m' := $UpdateMutation(m, ConcatVec($Dereference(m), ReverseVec(other)));
}

procedure {:inline 1} $1_vector_trim_reverse'$1_aptos_coin_AptosCoin'(m: $Mutation (Vec ($1_aptos_coin_AptosCoin)), new_len: int) returns (v: (Vec ($1_aptos_coin_AptosCoin)), m': $Mutation (Vec ($1_aptos_coin_AptosCoin))) {
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

procedure {:inline 1} $1_vector_trim'$1_aptos_coin_AptosCoin'(m: $Mutation (Vec ($1_aptos_coin_AptosCoin)), new_len: int) returns (v: (Vec ($1_aptos_coin_AptosCoin)), m': $Mutation (Vec ($1_aptos_coin_AptosCoin))) {
    var len: int;
    v := $Dereference(m);
    if (LenVec(v) < new_len) {
        call $ExecFailureAbort();
        return;
    }
    v := SliceVec(v, new_len, LenVec(v));
    m' := $UpdateMutation(m, SliceVec($Dereference(m), 0, new_len));
}

procedure {:inline 1} $1_vector_reverse_slice'$1_aptos_coin_AptosCoin'(m: $Mutation (Vec ($1_aptos_coin_AptosCoin)), left: int, right: int) returns (m': $Mutation (Vec ($1_aptos_coin_AptosCoin))) {
    var left_vec: Vec ($1_aptos_coin_AptosCoin);
    var mid_vec: Vec ($1_aptos_coin_AptosCoin);
    var right_vec: Vec ($1_aptos_coin_AptosCoin);
    var v: Vec ($1_aptos_coin_AptosCoin);
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

procedure {:inline 1} $1_vector_rotate'$1_aptos_coin_AptosCoin'(m: $Mutation (Vec ($1_aptos_coin_AptosCoin)), rot: int) returns (n: int, m': $Mutation (Vec ($1_aptos_coin_AptosCoin))) {
    var v: Vec ($1_aptos_coin_AptosCoin);
    var len: int;
    var left_vec: Vec ($1_aptos_coin_AptosCoin);
    var right_vec: Vec ($1_aptos_coin_AptosCoin);
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

procedure {:inline 1} $1_vector_rotate_slice'$1_aptos_coin_AptosCoin'(m: $Mutation (Vec ($1_aptos_coin_AptosCoin)), left: int, rot: int, right: int) returns (n: int, m': $Mutation (Vec ($1_aptos_coin_AptosCoin))) {
    var left_vec: Vec ($1_aptos_coin_AptosCoin);
    var mid_vec: Vec ($1_aptos_coin_AptosCoin);
    var right_vec: Vec ($1_aptos_coin_AptosCoin);
    var mid_left_vec: Vec ($1_aptos_coin_AptosCoin);
    var mid_right_vec: Vec ($1_aptos_coin_AptosCoin);
    var v: Vec ($1_aptos_coin_AptosCoin);
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

procedure {:inline 1} $1_vector_insert'$1_aptos_coin_AptosCoin'(m: $Mutation (Vec ($1_aptos_coin_AptosCoin)), i: int, e: $1_aptos_coin_AptosCoin) returns (m': $Mutation (Vec ($1_aptos_coin_AptosCoin))) {
    var left_vec: Vec ($1_aptos_coin_AptosCoin);
    var right_vec: Vec ($1_aptos_coin_AptosCoin);
    var v: Vec ($1_aptos_coin_AptosCoin);
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

procedure {:inline 1} $1_vector_length'$1_aptos_coin_AptosCoin'(v: Vec ($1_aptos_coin_AptosCoin)) returns (l: int) {
    l := LenVec(v);
}

function {:inline} $1_vector_$length'$1_aptos_coin_AptosCoin'(v: Vec ($1_aptos_coin_AptosCoin)): int {
    LenVec(v)
}

procedure {:inline 1} $1_vector_borrow'$1_aptos_coin_AptosCoin'(v: Vec ($1_aptos_coin_AptosCoin), i: int) returns (dst: $1_aptos_coin_AptosCoin) {
    if (!InRangeVec(v, i)) {
        call $ExecFailureAbort();
        return;
    }
    dst := ReadVec(v, i);
}

function {:inline} $1_vector_$borrow'$1_aptos_coin_AptosCoin'(v: Vec ($1_aptos_coin_AptosCoin), i: int): $1_aptos_coin_AptosCoin {
    ReadVec(v, i)
}

procedure {:inline 1} $1_vector_borrow_mut'$1_aptos_coin_AptosCoin'(m: $Mutation (Vec ($1_aptos_coin_AptosCoin)), index: int)
returns (dst: $Mutation ($1_aptos_coin_AptosCoin), m': $Mutation (Vec ($1_aptos_coin_AptosCoin)))
{
    var v: Vec ($1_aptos_coin_AptosCoin);
    v := $Dereference(m);
    if (!InRangeVec(v, index)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Mutation(l#$Mutation(m), ExtendVec(p#$Mutation(m), index), ReadVec(v, index));
    m' := m;
}

function {:inline} $1_vector_$borrow_mut'$1_aptos_coin_AptosCoin'(v: Vec ($1_aptos_coin_AptosCoin), i: int): $1_aptos_coin_AptosCoin {
    ReadVec(v, i)
}

procedure {:inline 1} $1_vector_destroy_empty'$1_aptos_coin_AptosCoin'(v: Vec ($1_aptos_coin_AptosCoin)) {
    if (!IsEmptyVec(v)) {
      call $ExecFailureAbort();
    }
}

procedure {:inline 1} $1_vector_swap'$1_aptos_coin_AptosCoin'(m: $Mutation (Vec ($1_aptos_coin_AptosCoin)), i: int, j: int) returns (m': $Mutation (Vec ($1_aptos_coin_AptosCoin)))
{
    var v: Vec ($1_aptos_coin_AptosCoin);
    v := $Dereference(m);
    if (!InRangeVec(v, i) || !InRangeVec(v, j)) {
        call $ExecFailureAbort();
        return;
    }
    m' := $UpdateMutation(m, SwapVec(v, i, j));
}

function {:inline} $1_vector_$swap'$1_aptos_coin_AptosCoin'(v: Vec ($1_aptos_coin_AptosCoin), i: int, j: int): Vec ($1_aptos_coin_AptosCoin) {
    SwapVec(v, i, j)
}

procedure {:inline 1} $1_vector_remove'$1_aptos_coin_AptosCoin'(m: $Mutation (Vec ($1_aptos_coin_AptosCoin)), i: int) returns (e: $1_aptos_coin_AptosCoin, m': $Mutation (Vec ($1_aptos_coin_AptosCoin)))
{
    var v: Vec ($1_aptos_coin_AptosCoin);

    v := $Dereference(m);

    if (!InRangeVec(v, i)) {
        call $ExecFailureAbort();
        return;
    }
    e := ReadVec(v, i);
    m' := $UpdateMutation(m, RemoveAtVec(v, i));
}

procedure {:inline 1} $1_vector_swap_remove'$1_aptos_coin_AptosCoin'(m: $Mutation (Vec ($1_aptos_coin_AptosCoin)), i: int) returns (e: $1_aptos_coin_AptosCoin, m': $Mutation (Vec ($1_aptos_coin_AptosCoin)))
{
    var len: int;
    var v: Vec ($1_aptos_coin_AptosCoin);

    v := $Dereference(m);
    len := LenVec(v);
    if (!InRangeVec(v, i)) {
        call $ExecFailureAbort();
        return;
    }
    e := ReadVec(v, i);
    m' := $UpdateMutation(m, RemoveVec(SwapVec(v, i, len-1)));
}

procedure {:inline 1} $1_vector_contains'$1_aptos_coin_AptosCoin'(v: Vec ($1_aptos_coin_AptosCoin), e: $1_aptos_coin_AptosCoin) returns (res: bool)  {
    res := $ContainsVec'$1_aptos_coin_AptosCoin'(v, e);
}

procedure {:inline 1}
$1_vector_index_of'$1_aptos_coin_AptosCoin'(v: Vec ($1_aptos_coin_AptosCoin), e: $1_aptos_coin_AptosCoin) returns (res1: bool, res2: int) {
    res2 := $IndexOfVec'$1_aptos_coin_AptosCoin'(v, e);
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

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:14:9+116, instance <vector<aggregator::Aggregator>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'$1_aggregator_Aggregator''($1_from_bcs_deserialize'vec'$1_aggregator_Aggregator''(b1), $1_from_bcs_deserialize'vec'$1_aggregator_Aggregator''(b2)) ==> $IsEqual'vec'u8''(b1, b2))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:14:9+116, instance <vector<optional_aggregator::Integer>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'$1_optional_aggregator_Integer''($1_from_bcs_deserialize'vec'$1_optional_aggregator_Integer''(b1), $1_from_bcs_deserialize'vec'$1_optional_aggregator_Integer''(b2)) ==> $IsEqual'vec'u8''(b1, b2))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:14:9+116, instance <vector<optional_aggregator::OptionalAggregator>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'$1_optional_aggregator_OptionalAggregator''($1_from_bcs_deserialize'vec'$1_optional_aggregator_OptionalAggregator''(b1), $1_from_bcs_deserialize'vec'$1_optional_aggregator_OptionalAggregator''(b2)) ==> $IsEqual'vec'u8''(b1, b2))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:14:9+116, instance <vector<aptos_coin::AptosCoin>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'$1_aptos_coin_AptosCoin''($1_from_bcs_deserialize'vec'$1_aptos_coin_AptosCoin''(b1), $1_from_bcs_deserialize'vec'$1_aptos_coin_AptosCoin''(b2)) ==> $IsEqual'vec'u8''(b1, b2))));

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

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:14:9+116, instance <option::Option<u64>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'$1_option_Option'u64''($1_from_bcs_deserialize'$1_option_Option'u64''(b1), $1_from_bcs_deserialize'$1_option_Option'u64''(b2)) ==> $IsEqual'vec'u8''(b1, b2))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:14:9+116, instance <option::Option<u128>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'$1_option_Option'u128''($1_from_bcs_deserialize'$1_option_Option'u128''(b1), $1_from_bcs_deserialize'$1_option_Option'u128''(b2)) ==> $IsEqual'vec'u8''(b1, b2))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:14:9+116, instance <option::Option<aggregator::Aggregator>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'$1_option_Option'$1_aggregator_Aggregator''($1_from_bcs_deserialize'$1_option_Option'$1_aggregator_Aggregator''(b1), $1_from_bcs_deserialize'$1_option_Option'$1_aggregator_Aggregator''(b2)) ==> $IsEqual'vec'u8''(b1, b2))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:14:9+116, instance <option::Option<optional_aggregator::Integer>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'$1_option_Option'$1_optional_aggregator_Integer''($1_from_bcs_deserialize'$1_option_Option'$1_optional_aggregator_Integer''(b1), $1_from_bcs_deserialize'$1_option_Option'$1_optional_aggregator_Integer''(b2)) ==> $IsEqual'vec'u8''(b1, b2))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:14:9+116, instance <option::Option<optional_aggregator::OptionalAggregator>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'$1_option_Option'$1_optional_aggregator_OptionalAggregator''($1_from_bcs_deserialize'$1_option_Option'$1_optional_aggregator_OptionalAggregator''(b1), $1_from_bcs_deserialize'$1_option_Option'$1_optional_aggregator_OptionalAggregator''(b2)) ==> $IsEqual'vec'u8''(b1, b2))));

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

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:14:9+116, instance <event::EventHandle<reconfiguration::NewEpochEvent>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'$1_event_EventHandle'$1_reconfiguration_NewEpochEvent''($1_from_bcs_deserialize'$1_event_EventHandle'$1_reconfiguration_NewEpochEvent''(b1), $1_from_bcs_deserialize'$1_event_EventHandle'$1_reconfiguration_NewEpochEvent''(b2)) ==> $IsEqual'vec'u8''(b1, b2))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:14:9+116, instance <event::EventHandle<aptos_governance::CreateProposalEvent>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'$1_event_EventHandle'$1_aptos_governance_CreateProposalEvent''($1_from_bcs_deserialize'$1_event_EventHandle'$1_aptos_governance_CreateProposalEvent''(b1), $1_from_bcs_deserialize'$1_event_EventHandle'$1_aptos_governance_CreateProposalEvent''(b2)) ==> $IsEqual'vec'u8''(b1, b2))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:14:9+116, instance <event::EventHandle<aptos_governance::VoteEvent>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'$1_event_EventHandle'$1_aptos_governance_VoteEvent''($1_from_bcs_deserialize'$1_event_EventHandle'$1_aptos_governance_VoteEvent''(b1), $1_from_bcs_deserialize'$1_event_EventHandle'$1_aptos_governance_VoteEvent''(b2)) ==> $IsEqual'vec'u8''(b1, b2))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:14:9+116, instance <event::EventHandle<aptos_governance::UpdateConfigEvent>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'$1_event_EventHandle'$1_aptos_governance_UpdateConfigEvent''($1_from_bcs_deserialize'$1_event_EventHandle'$1_aptos_governance_UpdateConfigEvent''(b1), $1_from_bcs_deserialize'$1_event_EventHandle'$1_aptos_governance_UpdateConfigEvent''(b2)) ==> $IsEqual'vec'u8''(b1, b2))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:14:9+116, instance <event::EventHandle<block::NewBlockEvent>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'$1_event_EventHandle'$1_block_NewBlockEvent''($1_from_bcs_deserialize'$1_event_EventHandle'$1_block_NewBlockEvent''(b1), $1_from_bcs_deserialize'$1_event_EventHandle'$1_block_NewBlockEvent''(b2)) ==> $IsEqual'vec'u8''(b1, b2))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:14:9+116, instance <event::EventHandle<block::UpdateEpochIntervalEvent>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'$1_event_EventHandle'$1_block_UpdateEpochIntervalEvent''($1_from_bcs_deserialize'$1_event_EventHandle'$1_block_UpdateEpochIntervalEvent''(b1), $1_from_bcs_deserialize'$1_event_EventHandle'$1_block_UpdateEpochIntervalEvent''(b2)) ==> $IsEqual'vec'u8''(b1, b2))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:14:9+116, instance <aggregator::Aggregator>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'$1_aggregator_Aggregator'($1_from_bcs_deserialize'$1_aggregator_Aggregator'(b1), $1_from_bcs_deserialize'$1_aggregator_Aggregator'(b2)) ==> $IsEqual'vec'u8''(b1, b2))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:14:9+116, instance <optional_aggregator::Integer>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'$1_optional_aggregator_Integer'($1_from_bcs_deserialize'$1_optional_aggregator_Integer'(b1), $1_from_bcs_deserialize'$1_optional_aggregator_Integer'(b2)) ==> $IsEqual'vec'u8''(b1, b2))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:14:9+116, instance <optional_aggregator::OptionalAggregator>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'$1_optional_aggregator_OptionalAggregator'($1_from_bcs_deserialize'$1_optional_aggregator_OptionalAggregator'(b1), $1_from_bcs_deserialize'$1_optional_aggregator_OptionalAggregator'(b2)) ==> $IsEqual'vec'u8''(b1, b2))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:14:9+116, instance <coin::BurnCapability<aptos_coin::AptosCoin>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'$1_coin_BurnCapability'$1_aptos_coin_AptosCoin''($1_from_bcs_deserialize'$1_coin_BurnCapability'$1_aptos_coin_AptosCoin''(b1), $1_from_bcs_deserialize'$1_coin_BurnCapability'$1_aptos_coin_AptosCoin''(b2)) ==> $IsEqual'vec'u8''(b1, b2))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:14:9+116, instance <coin::Coin<aptos_coin::AptosCoin>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'$1_coin_Coin'$1_aptos_coin_AptosCoin''($1_from_bcs_deserialize'$1_coin_Coin'$1_aptos_coin_AptosCoin''(b1), $1_from_bcs_deserialize'$1_coin_Coin'$1_aptos_coin_AptosCoin''(b2)) ==> $IsEqual'vec'u8''(b1, b2))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:14:9+116, instance <coin::CoinInfo<aptos_coin::AptosCoin>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'$1_coin_CoinInfo'$1_aptos_coin_AptosCoin''($1_from_bcs_deserialize'$1_coin_CoinInfo'$1_aptos_coin_AptosCoin''(b1), $1_from_bcs_deserialize'$1_coin_CoinInfo'$1_aptos_coin_AptosCoin''(b2)) ==> $IsEqual'vec'u8''(b1, b2))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:14:9+116, instance <coin::MintCapability<aptos_coin::AptosCoin>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'$1_coin_MintCapability'$1_aptos_coin_AptosCoin''($1_from_bcs_deserialize'$1_coin_MintCapability'$1_aptos_coin_AptosCoin''(b1), $1_from_bcs_deserialize'$1_coin_MintCapability'$1_aptos_coin_AptosCoin''(b2)) ==> $IsEqual'vec'u8''(b1, b2))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:14:9+116, instance <aptos_coin::AptosCoin>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'$1_aptos_coin_AptosCoin'($1_from_bcs_deserialize'$1_aptos_coin_AptosCoin'(b1), $1_from_bcs_deserialize'$1_aptos_coin_AptosCoin'(b2)) ==> $IsEqual'vec'u8''(b1, b2))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:14:9+116, instance <chain_status::GenesisEndMarker>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'$1_chain_status_GenesisEndMarker'($1_from_bcs_deserialize'$1_chain_status_GenesisEndMarker'(b1), $1_from_bcs_deserialize'$1_chain_status_GenesisEndMarker'(b2)) ==> $IsEqual'vec'u8''(b1, b2))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:14:9+116, instance <timestamp::CurrentTimeMicroseconds>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'$1_timestamp_CurrentTimeMicroseconds'($1_from_bcs_deserialize'$1_timestamp_CurrentTimeMicroseconds'(b1), $1_from_bcs_deserialize'$1_timestamp_CurrentTimeMicroseconds'(b2)) ==> $IsEqual'vec'u8''(b1, b2))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:14:9+116, instance <simple_map::SimpleMap<string::String, vector<u8>>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'$1_simple_map_SimpleMap'$1_string_String_vec'u8'''($1_from_bcs_deserialize'$1_simple_map_SimpleMap'$1_string_String_vec'u8'''(b1), $1_from_bcs_deserialize'$1_simple_map_SimpleMap'$1_string_String_vec'u8'''(b2)) ==> $IsEqual'vec'u8''(b1, b2))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:14:9+116, instance <voting::CreateProposalEvent>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'$1_voting_CreateProposalEvent'($1_from_bcs_deserialize'$1_voting_CreateProposalEvent'(b1), $1_from_bcs_deserialize'$1_voting_CreateProposalEvent'(b2)) ==> $IsEqual'vec'u8''(b1, b2))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:14:9+116, instance <voting::Proposal<governance_proposal::GovernanceProposal>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'$1_voting_Proposal'$1_governance_proposal_GovernanceProposal''($1_from_bcs_deserialize'$1_voting_Proposal'$1_governance_proposal_GovernanceProposal''(b1), $1_from_bcs_deserialize'$1_voting_Proposal'$1_governance_proposal_GovernanceProposal''(b2)) ==> $IsEqual'vec'u8''(b1, b2))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:14:9+116, instance <voting::VotingEvents>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'$1_voting_VotingEvents'($1_from_bcs_deserialize'$1_voting_VotingEvents'(b1), $1_from_bcs_deserialize'$1_voting_VotingEvents'(b2)) ==> $IsEqual'vec'u8''(b1, b2))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:14:9+116, instance <voting::VotingForum<governance_proposal::GovernanceProposal>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'$1_voting_VotingForum'$1_governance_proposal_GovernanceProposal''($1_from_bcs_deserialize'$1_voting_VotingForum'$1_governance_proposal_GovernanceProposal''(b1), $1_from_bcs_deserialize'$1_voting_VotingForum'$1_governance_proposal_GovernanceProposal''(b2)) ==> $IsEqual'vec'u8''(b1, b2))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:14:9+116, instance <staking_config::StakingConfig>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'$1_staking_config_StakingConfig'($1_from_bcs_deserialize'$1_staking_config_StakingConfig'(b1), $1_from_bcs_deserialize'$1_staking_config_StakingConfig'(b2)) ==> $IsEqual'vec'u8''(b1, b2))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:14:9+116, instance <stake::AptosCoinCapabilities>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'$1_stake_AptosCoinCapabilities'($1_from_bcs_deserialize'$1_stake_AptosCoinCapabilities'(b1), $1_from_bcs_deserialize'$1_stake_AptosCoinCapabilities'(b2)) ==> $IsEqual'vec'u8''(b1, b2))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:14:9+116, instance <stake::StakePool>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'$1_stake_StakePool'($1_from_bcs_deserialize'$1_stake_StakePool'(b1), $1_from_bcs_deserialize'$1_stake_StakePool'(b2)) ==> $IsEqual'vec'u8''(b1, b2))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:14:9+116, instance <stake::ValidatorConfig>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'$1_stake_ValidatorConfig'($1_from_bcs_deserialize'$1_stake_ValidatorConfig'(b1), $1_from_bcs_deserialize'$1_stake_ValidatorConfig'(b2)) ==> $IsEqual'vec'u8''(b1, b2))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:14:9+116, instance <stake::ValidatorInfo>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'$1_stake_ValidatorInfo'($1_from_bcs_deserialize'$1_stake_ValidatorInfo'(b1), $1_from_bcs_deserialize'$1_stake_ValidatorInfo'(b2)) ==> $IsEqual'vec'u8''(b1, b2))));

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

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:14:9+116, instance <aptos_governance::CreateProposalEvent>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'$1_aptos_governance_CreateProposalEvent'($1_from_bcs_deserialize'$1_aptos_governance_CreateProposalEvent'(b1), $1_from_bcs_deserialize'$1_aptos_governance_CreateProposalEvent'(b2)) ==> $IsEqual'vec'u8''(b1, b2))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:14:9+116, instance <aptos_governance::GovernanceConfig>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'$1_aptos_governance_GovernanceConfig'($1_from_bcs_deserialize'$1_aptos_governance_GovernanceConfig'(b1), $1_from_bcs_deserialize'$1_aptos_governance_GovernanceConfig'(b2)) ==> $IsEqual'vec'u8''(b1, b2))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:14:9+116, instance <aptos_governance::GovernanceEvents>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'$1_aptos_governance_GovernanceEvents'($1_from_bcs_deserialize'$1_aptos_governance_GovernanceEvents'(b1), $1_from_bcs_deserialize'$1_aptos_governance_GovernanceEvents'(b2)) ==> $IsEqual'vec'u8''(b1, b2))));

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

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:18:9+124, instance <vector<aggregator::Aggregator>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'bool'($1_from_bcs_deserializable'vec'$1_aggregator_Aggregator''(b1), $1_from_bcs_deserializable'vec'$1_aggregator_Aggregator''(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:18:9+124, instance <vector<optional_aggregator::Integer>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'bool'($1_from_bcs_deserializable'vec'$1_optional_aggregator_Integer''(b1), $1_from_bcs_deserializable'vec'$1_optional_aggregator_Integer''(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:18:9+124, instance <vector<optional_aggregator::OptionalAggregator>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'bool'($1_from_bcs_deserializable'vec'$1_optional_aggregator_OptionalAggregator''(b1), $1_from_bcs_deserializable'vec'$1_optional_aggregator_OptionalAggregator''(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:18:9+124, instance <vector<aptos_coin::AptosCoin>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'bool'($1_from_bcs_deserializable'vec'$1_aptos_coin_AptosCoin''(b1), $1_from_bcs_deserializable'vec'$1_aptos_coin_AptosCoin''(b2)))));

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

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:18:9+124, instance <option::Option<u64>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'bool'($1_from_bcs_deserializable'$1_option_Option'u64''(b1), $1_from_bcs_deserializable'$1_option_Option'u64''(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:18:9+124, instance <option::Option<u128>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'bool'($1_from_bcs_deserializable'$1_option_Option'u128''(b1), $1_from_bcs_deserializable'$1_option_Option'u128''(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:18:9+124, instance <option::Option<aggregator::Aggregator>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'bool'($1_from_bcs_deserializable'$1_option_Option'$1_aggregator_Aggregator''(b1), $1_from_bcs_deserializable'$1_option_Option'$1_aggregator_Aggregator''(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:18:9+124, instance <option::Option<optional_aggregator::Integer>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'bool'($1_from_bcs_deserializable'$1_option_Option'$1_optional_aggregator_Integer''(b1), $1_from_bcs_deserializable'$1_option_Option'$1_optional_aggregator_Integer''(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:18:9+124, instance <option::Option<optional_aggregator::OptionalAggregator>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'bool'($1_from_bcs_deserializable'$1_option_Option'$1_optional_aggregator_OptionalAggregator''(b1), $1_from_bcs_deserializable'$1_option_Option'$1_optional_aggregator_OptionalAggregator''(b2)))));

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

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:18:9+124, instance <event::EventHandle<reconfiguration::NewEpochEvent>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'bool'($1_from_bcs_deserializable'$1_event_EventHandle'$1_reconfiguration_NewEpochEvent''(b1), $1_from_bcs_deserializable'$1_event_EventHandle'$1_reconfiguration_NewEpochEvent''(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:18:9+124, instance <event::EventHandle<aptos_governance::CreateProposalEvent>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'bool'($1_from_bcs_deserializable'$1_event_EventHandle'$1_aptos_governance_CreateProposalEvent''(b1), $1_from_bcs_deserializable'$1_event_EventHandle'$1_aptos_governance_CreateProposalEvent''(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:18:9+124, instance <event::EventHandle<aptos_governance::VoteEvent>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'bool'($1_from_bcs_deserializable'$1_event_EventHandle'$1_aptos_governance_VoteEvent''(b1), $1_from_bcs_deserializable'$1_event_EventHandle'$1_aptos_governance_VoteEvent''(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:18:9+124, instance <event::EventHandle<aptos_governance::UpdateConfigEvent>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'bool'($1_from_bcs_deserializable'$1_event_EventHandle'$1_aptos_governance_UpdateConfigEvent''(b1), $1_from_bcs_deserializable'$1_event_EventHandle'$1_aptos_governance_UpdateConfigEvent''(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:18:9+124, instance <event::EventHandle<block::NewBlockEvent>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'bool'($1_from_bcs_deserializable'$1_event_EventHandle'$1_block_NewBlockEvent''(b1), $1_from_bcs_deserializable'$1_event_EventHandle'$1_block_NewBlockEvent''(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:18:9+124, instance <event::EventHandle<block::UpdateEpochIntervalEvent>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'bool'($1_from_bcs_deserializable'$1_event_EventHandle'$1_block_UpdateEpochIntervalEvent''(b1), $1_from_bcs_deserializable'$1_event_EventHandle'$1_block_UpdateEpochIntervalEvent''(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:18:9+124, instance <aggregator::Aggregator>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'bool'($1_from_bcs_deserializable'$1_aggregator_Aggregator'(b1), $1_from_bcs_deserializable'$1_aggregator_Aggregator'(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:18:9+124, instance <optional_aggregator::Integer>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'bool'($1_from_bcs_deserializable'$1_optional_aggregator_Integer'(b1), $1_from_bcs_deserializable'$1_optional_aggregator_Integer'(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:18:9+124, instance <optional_aggregator::OptionalAggregator>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'bool'($1_from_bcs_deserializable'$1_optional_aggregator_OptionalAggregator'(b1), $1_from_bcs_deserializable'$1_optional_aggregator_OptionalAggregator'(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:18:9+124, instance <coin::BurnCapability<aptos_coin::AptosCoin>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'bool'($1_from_bcs_deserializable'$1_coin_BurnCapability'$1_aptos_coin_AptosCoin''(b1), $1_from_bcs_deserializable'$1_coin_BurnCapability'$1_aptos_coin_AptosCoin''(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:18:9+124, instance <coin::Coin<aptos_coin::AptosCoin>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'bool'($1_from_bcs_deserializable'$1_coin_Coin'$1_aptos_coin_AptosCoin''(b1), $1_from_bcs_deserializable'$1_coin_Coin'$1_aptos_coin_AptosCoin''(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:18:9+124, instance <coin::CoinInfo<aptos_coin::AptosCoin>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'bool'($1_from_bcs_deserializable'$1_coin_CoinInfo'$1_aptos_coin_AptosCoin''(b1), $1_from_bcs_deserializable'$1_coin_CoinInfo'$1_aptos_coin_AptosCoin''(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:18:9+124, instance <coin::MintCapability<aptos_coin::AptosCoin>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'bool'($1_from_bcs_deserializable'$1_coin_MintCapability'$1_aptos_coin_AptosCoin''(b1), $1_from_bcs_deserializable'$1_coin_MintCapability'$1_aptos_coin_AptosCoin''(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:18:9+124, instance <aptos_coin::AptosCoin>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'bool'($1_from_bcs_deserializable'$1_aptos_coin_AptosCoin'(b1), $1_from_bcs_deserializable'$1_aptos_coin_AptosCoin'(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:18:9+124, instance <chain_status::GenesisEndMarker>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'bool'($1_from_bcs_deserializable'$1_chain_status_GenesisEndMarker'(b1), $1_from_bcs_deserializable'$1_chain_status_GenesisEndMarker'(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:18:9+124, instance <timestamp::CurrentTimeMicroseconds>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'bool'($1_from_bcs_deserializable'$1_timestamp_CurrentTimeMicroseconds'(b1), $1_from_bcs_deserializable'$1_timestamp_CurrentTimeMicroseconds'(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:18:9+124, instance <simple_map::SimpleMap<string::String, vector<u8>>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'bool'($1_from_bcs_deserializable'$1_simple_map_SimpleMap'$1_string_String_vec'u8'''(b1), $1_from_bcs_deserializable'$1_simple_map_SimpleMap'$1_string_String_vec'u8'''(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:18:9+124, instance <voting::CreateProposalEvent>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'bool'($1_from_bcs_deserializable'$1_voting_CreateProposalEvent'(b1), $1_from_bcs_deserializable'$1_voting_CreateProposalEvent'(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:18:9+124, instance <voting::Proposal<governance_proposal::GovernanceProposal>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'bool'($1_from_bcs_deserializable'$1_voting_Proposal'$1_governance_proposal_GovernanceProposal''(b1), $1_from_bcs_deserializable'$1_voting_Proposal'$1_governance_proposal_GovernanceProposal''(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:18:9+124, instance <voting::VotingEvents>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'bool'($1_from_bcs_deserializable'$1_voting_VotingEvents'(b1), $1_from_bcs_deserializable'$1_voting_VotingEvents'(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:18:9+124, instance <voting::VotingForum<governance_proposal::GovernanceProposal>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'bool'($1_from_bcs_deserializable'$1_voting_VotingForum'$1_governance_proposal_GovernanceProposal''(b1), $1_from_bcs_deserializable'$1_voting_VotingForum'$1_governance_proposal_GovernanceProposal''(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:18:9+124, instance <staking_config::StakingConfig>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'bool'($1_from_bcs_deserializable'$1_staking_config_StakingConfig'(b1), $1_from_bcs_deserializable'$1_staking_config_StakingConfig'(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:18:9+124, instance <stake::AptosCoinCapabilities>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'bool'($1_from_bcs_deserializable'$1_stake_AptosCoinCapabilities'(b1), $1_from_bcs_deserializable'$1_stake_AptosCoinCapabilities'(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:18:9+124, instance <stake::StakePool>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'bool'($1_from_bcs_deserializable'$1_stake_StakePool'(b1), $1_from_bcs_deserializable'$1_stake_StakePool'(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:18:9+124, instance <stake::ValidatorConfig>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'bool'($1_from_bcs_deserializable'$1_stake_ValidatorConfig'(b1), $1_from_bcs_deserializable'$1_stake_ValidatorConfig'(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:18:9+124, instance <stake::ValidatorInfo>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'bool'($1_from_bcs_deserializable'$1_stake_ValidatorInfo'(b1), $1_from_bcs_deserializable'$1_stake_ValidatorInfo'(b2)))));

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

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:18:9+124, instance <aptos_governance::CreateProposalEvent>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'bool'($1_from_bcs_deserializable'$1_aptos_governance_CreateProposalEvent'(b1), $1_from_bcs_deserializable'$1_aptos_governance_CreateProposalEvent'(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:18:9+124, instance <aptos_governance::GovernanceConfig>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'bool'($1_from_bcs_deserializable'$1_aptos_governance_GovernanceConfig'(b1), $1_from_bcs_deserializable'$1_aptos_governance_GovernanceConfig'(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:18:9+124, instance <aptos_governance::GovernanceEvents>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'bool'($1_from_bcs_deserializable'$1_aptos_governance_GovernanceEvents'(b1), $1_from_bcs_deserializable'$1_aptos_governance_GovernanceEvents'(b2)))));

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

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:21:9+118, instance <vector<aggregator::Aggregator>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'vec'$1_aggregator_Aggregator''($1_from_bcs_deserialize'vec'$1_aggregator_Aggregator''(b1), $1_from_bcs_deserialize'vec'$1_aggregator_Aggregator''(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:21:9+118, instance <vector<optional_aggregator::Integer>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'vec'$1_optional_aggregator_Integer''($1_from_bcs_deserialize'vec'$1_optional_aggregator_Integer''(b1), $1_from_bcs_deserialize'vec'$1_optional_aggregator_Integer''(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:21:9+118, instance <vector<optional_aggregator::OptionalAggregator>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'vec'$1_optional_aggregator_OptionalAggregator''($1_from_bcs_deserialize'vec'$1_optional_aggregator_OptionalAggregator''(b1), $1_from_bcs_deserialize'vec'$1_optional_aggregator_OptionalAggregator''(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:21:9+118, instance <vector<aptos_coin::AptosCoin>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'vec'$1_aptos_coin_AptosCoin''($1_from_bcs_deserialize'vec'$1_aptos_coin_AptosCoin''(b1), $1_from_bcs_deserialize'vec'$1_aptos_coin_AptosCoin''(b2)))));

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

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:21:9+118, instance <option::Option<u64>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'$1_option_Option'u64''($1_from_bcs_deserialize'$1_option_Option'u64''(b1), $1_from_bcs_deserialize'$1_option_Option'u64''(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:21:9+118, instance <option::Option<u128>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'$1_option_Option'u128''($1_from_bcs_deserialize'$1_option_Option'u128''(b1), $1_from_bcs_deserialize'$1_option_Option'u128''(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:21:9+118, instance <option::Option<aggregator::Aggregator>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'$1_option_Option'$1_aggregator_Aggregator''($1_from_bcs_deserialize'$1_option_Option'$1_aggregator_Aggregator''(b1), $1_from_bcs_deserialize'$1_option_Option'$1_aggregator_Aggregator''(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:21:9+118, instance <option::Option<optional_aggregator::Integer>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'$1_option_Option'$1_optional_aggregator_Integer''($1_from_bcs_deserialize'$1_option_Option'$1_optional_aggregator_Integer''(b1), $1_from_bcs_deserialize'$1_option_Option'$1_optional_aggregator_Integer''(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:21:9+118, instance <option::Option<optional_aggregator::OptionalAggregator>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'$1_option_Option'$1_optional_aggregator_OptionalAggregator''($1_from_bcs_deserialize'$1_option_Option'$1_optional_aggregator_OptionalAggregator''(b1), $1_from_bcs_deserialize'$1_option_Option'$1_optional_aggregator_OptionalAggregator''(b2)))));

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

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:21:9+118, instance <event::EventHandle<reconfiguration::NewEpochEvent>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'$1_event_EventHandle'$1_reconfiguration_NewEpochEvent''($1_from_bcs_deserialize'$1_event_EventHandle'$1_reconfiguration_NewEpochEvent''(b1), $1_from_bcs_deserialize'$1_event_EventHandle'$1_reconfiguration_NewEpochEvent''(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:21:9+118, instance <event::EventHandle<aptos_governance::CreateProposalEvent>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'$1_event_EventHandle'$1_aptos_governance_CreateProposalEvent''($1_from_bcs_deserialize'$1_event_EventHandle'$1_aptos_governance_CreateProposalEvent''(b1), $1_from_bcs_deserialize'$1_event_EventHandle'$1_aptos_governance_CreateProposalEvent''(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:21:9+118, instance <event::EventHandle<aptos_governance::VoteEvent>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'$1_event_EventHandle'$1_aptos_governance_VoteEvent''($1_from_bcs_deserialize'$1_event_EventHandle'$1_aptos_governance_VoteEvent''(b1), $1_from_bcs_deserialize'$1_event_EventHandle'$1_aptos_governance_VoteEvent''(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:21:9+118, instance <event::EventHandle<aptos_governance::UpdateConfigEvent>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'$1_event_EventHandle'$1_aptos_governance_UpdateConfigEvent''($1_from_bcs_deserialize'$1_event_EventHandle'$1_aptos_governance_UpdateConfigEvent''(b1), $1_from_bcs_deserialize'$1_event_EventHandle'$1_aptos_governance_UpdateConfigEvent''(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:21:9+118, instance <event::EventHandle<block::NewBlockEvent>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'$1_event_EventHandle'$1_block_NewBlockEvent''($1_from_bcs_deserialize'$1_event_EventHandle'$1_block_NewBlockEvent''(b1), $1_from_bcs_deserialize'$1_event_EventHandle'$1_block_NewBlockEvent''(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:21:9+118, instance <event::EventHandle<block::UpdateEpochIntervalEvent>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'$1_event_EventHandle'$1_block_UpdateEpochIntervalEvent''($1_from_bcs_deserialize'$1_event_EventHandle'$1_block_UpdateEpochIntervalEvent''(b1), $1_from_bcs_deserialize'$1_event_EventHandle'$1_block_UpdateEpochIntervalEvent''(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:21:9+118, instance <aggregator::Aggregator>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'$1_aggregator_Aggregator'($1_from_bcs_deserialize'$1_aggregator_Aggregator'(b1), $1_from_bcs_deserialize'$1_aggregator_Aggregator'(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:21:9+118, instance <optional_aggregator::Integer>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'$1_optional_aggregator_Integer'($1_from_bcs_deserialize'$1_optional_aggregator_Integer'(b1), $1_from_bcs_deserialize'$1_optional_aggregator_Integer'(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:21:9+118, instance <optional_aggregator::OptionalAggregator>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'$1_optional_aggregator_OptionalAggregator'($1_from_bcs_deserialize'$1_optional_aggregator_OptionalAggregator'(b1), $1_from_bcs_deserialize'$1_optional_aggregator_OptionalAggregator'(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:21:9+118, instance <coin::BurnCapability<aptos_coin::AptosCoin>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'$1_coin_BurnCapability'$1_aptos_coin_AptosCoin''($1_from_bcs_deserialize'$1_coin_BurnCapability'$1_aptos_coin_AptosCoin''(b1), $1_from_bcs_deserialize'$1_coin_BurnCapability'$1_aptos_coin_AptosCoin''(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:21:9+118, instance <coin::Coin<aptos_coin::AptosCoin>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'$1_coin_Coin'$1_aptos_coin_AptosCoin''($1_from_bcs_deserialize'$1_coin_Coin'$1_aptos_coin_AptosCoin''(b1), $1_from_bcs_deserialize'$1_coin_Coin'$1_aptos_coin_AptosCoin''(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:21:9+118, instance <coin::CoinInfo<aptos_coin::AptosCoin>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'$1_coin_CoinInfo'$1_aptos_coin_AptosCoin''($1_from_bcs_deserialize'$1_coin_CoinInfo'$1_aptos_coin_AptosCoin''(b1), $1_from_bcs_deserialize'$1_coin_CoinInfo'$1_aptos_coin_AptosCoin''(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:21:9+118, instance <coin::MintCapability<aptos_coin::AptosCoin>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'$1_coin_MintCapability'$1_aptos_coin_AptosCoin''($1_from_bcs_deserialize'$1_coin_MintCapability'$1_aptos_coin_AptosCoin''(b1), $1_from_bcs_deserialize'$1_coin_MintCapability'$1_aptos_coin_AptosCoin''(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:21:9+118, instance <aptos_coin::AptosCoin>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'$1_aptos_coin_AptosCoin'($1_from_bcs_deserialize'$1_aptos_coin_AptosCoin'(b1), $1_from_bcs_deserialize'$1_aptos_coin_AptosCoin'(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:21:9+118, instance <chain_status::GenesisEndMarker>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'$1_chain_status_GenesisEndMarker'($1_from_bcs_deserialize'$1_chain_status_GenesisEndMarker'(b1), $1_from_bcs_deserialize'$1_chain_status_GenesisEndMarker'(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:21:9+118, instance <timestamp::CurrentTimeMicroseconds>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'$1_timestamp_CurrentTimeMicroseconds'($1_from_bcs_deserialize'$1_timestamp_CurrentTimeMicroseconds'(b1), $1_from_bcs_deserialize'$1_timestamp_CurrentTimeMicroseconds'(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:21:9+118, instance <simple_map::SimpleMap<string::String, vector<u8>>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'$1_simple_map_SimpleMap'$1_string_String_vec'u8'''($1_from_bcs_deserialize'$1_simple_map_SimpleMap'$1_string_String_vec'u8'''(b1), $1_from_bcs_deserialize'$1_simple_map_SimpleMap'$1_string_String_vec'u8'''(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:21:9+118, instance <voting::CreateProposalEvent>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'$1_voting_CreateProposalEvent'($1_from_bcs_deserialize'$1_voting_CreateProposalEvent'(b1), $1_from_bcs_deserialize'$1_voting_CreateProposalEvent'(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:21:9+118, instance <voting::Proposal<governance_proposal::GovernanceProposal>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'$1_voting_Proposal'$1_governance_proposal_GovernanceProposal''($1_from_bcs_deserialize'$1_voting_Proposal'$1_governance_proposal_GovernanceProposal''(b1), $1_from_bcs_deserialize'$1_voting_Proposal'$1_governance_proposal_GovernanceProposal''(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:21:9+118, instance <voting::VotingEvents>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'$1_voting_VotingEvents'($1_from_bcs_deserialize'$1_voting_VotingEvents'(b1), $1_from_bcs_deserialize'$1_voting_VotingEvents'(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:21:9+118, instance <voting::VotingForum<governance_proposal::GovernanceProposal>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'$1_voting_VotingForum'$1_governance_proposal_GovernanceProposal''($1_from_bcs_deserialize'$1_voting_VotingForum'$1_governance_proposal_GovernanceProposal''(b1), $1_from_bcs_deserialize'$1_voting_VotingForum'$1_governance_proposal_GovernanceProposal''(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:21:9+118, instance <staking_config::StakingConfig>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'$1_staking_config_StakingConfig'($1_from_bcs_deserialize'$1_staking_config_StakingConfig'(b1), $1_from_bcs_deserialize'$1_staking_config_StakingConfig'(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:21:9+118, instance <stake::AptosCoinCapabilities>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'$1_stake_AptosCoinCapabilities'($1_from_bcs_deserialize'$1_stake_AptosCoinCapabilities'(b1), $1_from_bcs_deserialize'$1_stake_AptosCoinCapabilities'(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:21:9+118, instance <stake::StakePool>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'$1_stake_StakePool'($1_from_bcs_deserialize'$1_stake_StakePool'(b1), $1_from_bcs_deserialize'$1_stake_StakePool'(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:21:9+118, instance <stake::ValidatorConfig>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'$1_stake_ValidatorConfig'($1_from_bcs_deserialize'$1_stake_ValidatorConfig'(b1), $1_from_bcs_deserialize'$1_stake_ValidatorConfig'(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:21:9+118, instance <stake::ValidatorInfo>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'$1_stake_ValidatorInfo'($1_from_bcs_deserialize'$1_stake_ValidatorInfo'(b1), $1_from_bcs_deserialize'$1_stake_ValidatorInfo'(b2)))));

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

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:21:9+118, instance <aptos_governance::CreateProposalEvent>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'$1_aptos_governance_CreateProposalEvent'($1_from_bcs_deserialize'$1_aptos_governance_CreateProposalEvent'(b1), $1_from_bcs_deserialize'$1_aptos_governance_CreateProposalEvent'(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:21:9+118, instance <aptos_governance::GovernanceConfig>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'$1_aptos_governance_GovernanceConfig'($1_from_bcs_deserialize'$1_aptos_governance_GovernanceConfig'(b1), $1_from_bcs_deserialize'$1_aptos_governance_GovernanceConfig'(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:21:9+118, instance <aptos_governance::GovernanceEvents>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'$1_aptos_governance_GovernanceEvents'($1_from_bcs_deserialize'$1_aptos_governance_GovernanceEvents'(b1), $1_from_bcs_deserialize'$1_aptos_governance_GovernanceEvents'(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:21:9+118, instance <block::BlockResource>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'$1_block_BlockResource'($1_from_bcs_deserialize'$1_block_BlockResource'(b1), $1_from_bcs_deserialize'$1_block_BlockResource'(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:21:9+118, instance <#0>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'#0'($1_from_bcs_deserialize'#0'(b1), $1_from_bcs_deserialize'#0'(b2)))));

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/../move-stdlib/sources/vector.move:143:5+86
function {:inline} $1_vector_$is_empty'u64'(v: Vec (int)): bool {
    $IsEqual'u64'($1_vector_$length'u64'(v), 0)
}

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/../move-stdlib/sources/vector.move:143:5+86
function {:inline} $1_vector_$is_empty'u128'(v: Vec (int)): bool {
    $IsEqual'u64'($1_vector_$length'u128'(v), 0)
}

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/../move-stdlib/sources/vector.move:143:5+86
function {:inline} $1_vector_$is_empty'$1_aggregator_Aggregator'(v: Vec ($1_aggregator_Aggregator)): bool {
    $IsEqual'u64'($1_vector_$length'$1_aggregator_Aggregator'(v), 0)
}

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/../move-stdlib/sources/vector.move:143:5+86
function {:inline} $1_vector_$is_empty'$1_optional_aggregator_Integer'(v: Vec ($1_optional_aggregator_Integer)): bool {
    $IsEqual'u64'($1_vector_$length'$1_optional_aggregator_Integer'(v), 0)
}

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/../move-stdlib/sources/vector.move:143:5+86
function {:inline} $1_vector_$is_empty'$1_optional_aggregator_OptionalAggregator'(v: Vec ($1_optional_aggregator_OptionalAggregator)): bool {
    $IsEqual'u64'($1_vector_$length'$1_optional_aggregator_OptionalAggregator'(v), 0)
}

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/../move-stdlib/sources/option.move:102:5+145
function {:inline} $1_option_$borrow'u64'(t: $1_option_Option'u64'): int {
    $1_vector_$borrow'u64'($vec#$1_option_Option'u64'(t), 0)
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
function {:inline} $1_option_$is_none'u64'(t: $1_option_Option'u64'): bool {
    $1_vector_$is_empty'u64'($vec#$1_option_Option'u64'(t))
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
function {:inline} $1_option_$is_some'u64'(t: $1_option_Option'u64'): bool {
    !$1_vector_$is_empty'u64'($vec#$1_option_Option'u64'(t))
}

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/../move-stdlib/sources/option.move:74:5+96
function {:inline} $1_option_$is_some'$1_aggregator_Aggregator'(t: $1_option_Option'$1_aggregator_Aggregator'): bool {
    !$1_vector_$is_empty'$1_aggregator_Aggregator'($vec#$1_option_Option'$1_aggregator_Aggregator'(t))
}

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/../move-stdlib/sources/option.move:74:5+96
function {:inline} $1_option_$is_some'$1_optional_aggregator_Integer'(t: $1_option_Option'$1_optional_aggregator_Integer'): bool {
    !$1_vector_$is_empty'$1_optional_aggregator_Integer'($vec#$1_option_Option'$1_optional_aggregator_Integer'(t))
}

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/../move-stdlib/sources/option.move:34:10+78
function {:inline} $1_option_spec_none'u128'(): $1_option_Option'u128' {
    $1_option_Option'u128'($EmptyVec'u128'())
}

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/../move-stdlib/sources/option.move:47:10+89
function {:inline} $1_option_spec_some'u128'(e: int): $1_option_Option'u128' {
    $1_option_Option'u128'(MakeVec1(e))
}

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/../move-stdlib/sources/option.move:47:10+89
function {:inline} $1_option_spec_some'$1_governance_proposal_GovernanceProposal'(e: $1_governance_proposal_GovernanceProposal): $1_option_Option'$1_governance_proposal_GovernanceProposal' {
    $1_option_Option'$1_governance_proposal_GovernanceProposal'(MakeVec1(e))
}

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/../move-stdlib/sources/option.move:69:10+91
function {:inline} $1_option_spec_is_none'u128'(t: $1_option_Option'u128'): bool {
    $1_vector_$is_empty'u128'($vec#$1_option_Option'u128'(t))
}

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/../move-stdlib/sources/option.move:69:10+91
function {:inline} $1_option_spec_is_none'$1_aggregator_Aggregator'(t: $1_option_Option'$1_aggregator_Aggregator'): bool {
    $1_vector_$is_empty'$1_aggregator_Aggregator'($vec#$1_option_Option'$1_aggregator_Aggregator'(t))
}

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/../move-stdlib/sources/option.move:69:10+91
function {:inline} $1_option_spec_is_none'$1_optional_aggregator_Integer'(t: $1_option_Option'$1_optional_aggregator_Integer'): bool {
    $1_vector_$is_empty'$1_optional_aggregator_Integer'($vec#$1_option_Option'$1_optional_aggregator_Integer'(t))
}

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/../move-stdlib/sources/option.move:69:10+91
function {:inline} $1_option_spec_is_none'$1_optional_aggregator_OptionalAggregator'(t: $1_option_Option'$1_optional_aggregator_OptionalAggregator'): bool {
    $1_vector_$is_empty'$1_optional_aggregator_OptionalAggregator'($vec#$1_option_Option'$1_optional_aggregator_OptionalAggregator'(t))
}

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/../move-stdlib/sources/option.move:82:10+92
function {:inline} $1_option_spec_is_some'u64'(t: $1_option_Option'u64'): bool {
    !$1_vector_$is_empty'u64'($vec#$1_option_Option'u64'(t))
}

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/../move-stdlib/sources/option.move:82:10+92
function {:inline} $1_option_spec_is_some'u128'(t: $1_option_Option'u128'): bool {
    !$1_vector_$is_empty'u128'($vec#$1_option_Option'u128'(t))
}

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/../move-stdlib/sources/option.move:82:10+92
function {:inline} $1_option_spec_is_some'$1_aggregator_Aggregator'(t: $1_option_Option'$1_aggregator_Aggregator'): bool {
    !$1_vector_$is_empty'$1_aggregator_Aggregator'($vec#$1_option_Option'$1_aggregator_Aggregator'(t))
}

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/../move-stdlib/sources/option.move:82:10+92
function {:inline} $1_option_spec_is_some'$1_optional_aggregator_OptionalAggregator'(t: $1_option_Option'$1_optional_aggregator_OptionalAggregator'): bool {
    !$1_vector_$is_empty'$1_optional_aggregator_OptionalAggregator'($vec#$1_option_Option'$1_optional_aggregator_OptionalAggregator'(t))
}

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/../move-stdlib/sources/option.move:111:10+78
function {:inline} $1_option_spec_borrow'u128'(t: $1_option_Option'u128'): int {
    ReadVec($vec#$1_option_Option'u128'(t), 0)
}

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/../move-stdlib/sources/option.move:111:10+78
function {:inline} $1_option_spec_borrow'$1_aggregator_Aggregator'(t: $1_option_Option'$1_aggregator_Aggregator'): $1_aggregator_Aggregator {
    ReadVec($vec#$1_option_Option'$1_aggregator_Aggregator'(t), 0)
}

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/../move-stdlib/sources/option.move:111:10+78
function {:inline} $1_option_spec_borrow'$1_optional_aggregator_Integer'(t: $1_option_Option'$1_optional_aggregator_Integer'): $1_optional_aggregator_Integer {
    ReadVec($vec#$1_option_Option'$1_optional_aggregator_Integer'(t), 0)
}

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/../move-stdlib/sources/option.move:111:10+78
function {:inline} $1_option_spec_borrow'$1_optional_aggregator_OptionalAggregator'(t: $1_option_Option'$1_optional_aggregator_OptionalAggregator'): $1_optional_aggregator_OptionalAggregator {
    ReadVec($vec#$1_option_Option'$1_optional_aggregator_OptionalAggregator'(t), 0)
}

// struct option::Option<u64> at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/../move-stdlib/sources/option.move:7:5+81
type {:datatype} $1_option_Option'u64';
function {:constructor} $1_option_Option'u64'($vec: Vec (int)): $1_option_Option'u64';
function {:inline} $Update'$1_option_Option'u64''_vec(s: $1_option_Option'u64', x: Vec (int)): $1_option_Option'u64' {
    $1_option_Option'u64'(x)
}
function $IsValid'$1_option_Option'u64''(s: $1_option_Option'u64'): bool {
    $IsValid'vec'u64''($vec#$1_option_Option'u64'(s))
}
function {:inline} $IsEqual'$1_option_Option'u64''(s1: $1_option_Option'u64', s2: $1_option_Option'u64'): bool {
    $IsEqual'vec'u64''($vec#$1_option_Option'u64'(s1), $vec#$1_option_Option'u64'(s2))}

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

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/../move-stdlib/sources/string.move:43:5+75
function {:inline} $1_string_$length(s: $1_string_String): int {
    $1_vector_$length'u8'($bytes#$1_string_String(s))
}

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/../move-stdlib/sources/string.move:18:5+133
function {:inline} $1_string_$utf8(bytes: Vec (int)): $1_string_String {
    $1_string_String(bytes)
}

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/../move-stdlib/sources/string.spec.move:23:10+70
function {:inline} $1_string_spec_utf8(bytes: Vec (int)): $1_string_String {
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

// fun string::length [baseline] at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/../move-stdlib/sources/string.move:43:5+75
procedure {:inline 1} $1_string_length(_$t0: $1_string_String) returns ($ret0: int)
{
    // declare local variables
    var $t1: Vec (int);
    var $t2: int;
    var $t3: int;
    var $t0: $1_string_String;
    var $temp_0'$1_string_String': $1_string_String;
    var $temp_0'u64': int;
    $t0 := _$t0;

    // bytecode translation starts here
    // trace_local[s]($t0) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/../move-stdlib/sources/string.move:43:5+1
    assume {:print "$at(15,1295,1296)"} true;
    assume {:print "$track_local(2,10,0):", $t0} $t0 == $t0;

    // $t1 := get_field<string::String>.bytes($t0) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/../move-stdlib/sources/string.move:44:24+8
    assume {:print "$at(15,1355,1363)"} true;
    $t1 := $bytes#$1_string_String($t0);

    // $t2 := vector::length<u8>($t1) on_abort goto L2 with $t3 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/../move-stdlib/sources/string.move:44:9+24
    call $t2 := $1_vector_length'u8'($t1);
    if ($abort_flag) {
        assume {:print "$at(15,1340,1364)"} true;
        $t3 := $abort_code;
        assume {:print "$track_abort(2,10):", $t3} $t3 == $t3;
        goto L2;
    }

    // trace_return[0]($t2) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/../move-stdlib/sources/string.move:44:9+24
    assume {:print "$track_return(2,10,0):", $t2} $t2 == $t2;

    // label L1 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/../move-stdlib/sources/string.move:45:5+1
    assume {:print "$at(15,1369,1370)"} true;
L1:

    // return $t2 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/../move-stdlib/sources/string.move:45:5+1
    assume {:print "$at(15,1369,1370)"} true;
    $ret0 := $t2;
    return;

    // label L2 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/../move-stdlib/sources/string.move:45:5+1
L2:

    // abort($t3) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/../move-stdlib/sources/string.move:45:5+1
    assume {:print "$at(15,1369,1370)"} true;
    $abort_code := $t3;
    $abort_flag := true;
    return;

}

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

// fun signer::address_of [baseline] at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/../move-stdlib/sources/signer.move:12:5+77
procedure {:inline 1} $1_signer_address_of(_$t0: $signer) returns ($ret0: int)
{
    // declare local variables
    var $t1: int;
    var $t2: int;
    var $t0: $signer;
    var $temp_0'address': int;
    var $temp_0'signer': $signer;
    $t0 := _$t0;

    // bytecode translation starts here
    // trace_local[s]($t0) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/../move-stdlib/sources/signer.move:12:5+1
    assume {:print "$at(14,396,397)"} true;
    assume {:print "$track_local(3,0,0):", $t0} $t0 == $t0;

    // $t1 := signer::borrow_address($t0) on_abort goto L2 with $t2 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/../move-stdlib/sources/signer.move:13:10+17
    assume {:print "$at(14,450,467)"} true;
    call $t1 := $1_signer_borrow_address($t0);
    if ($abort_flag) {
        assume {:print "$at(14,450,467)"} true;
        $t2 := $abort_code;
        assume {:print "$track_abort(3,0):", $t2} $t2 == $t2;
        goto L2;
    }

    // trace_return[0]($t1) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/../move-stdlib/sources/signer.move:13:9+18
    assume {:print "$track_return(3,0,0):", $t1} $t1 == $t1;

    // label L1 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/../move-stdlib/sources/signer.move:14:5+1
    assume {:print "$at(14,472,473)"} true;
L1:

    // return $t1 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/../move-stdlib/sources/signer.move:14:5+1
    assume {:print "$at(14,472,473)"} true;
    $ret0 := $t1;
    return;

    // label L2 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/../move-stdlib/sources/signer.move:14:5+1
L2:

    // abort($t2) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/../move-stdlib/sources/signer.move:14:5+1
    assume {:print "$at(14,472,473)"} true;
    $abort_code := $t2;
    $abort_flag := true;
    return;

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
function  $1_from_bcs_deserialize'vec'$1_aptos_coin_AptosCoin''(bytes: Vec (int)): Vec ($1_aptos_coin_AptosCoin);
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserialize'vec'$1_aptos_coin_AptosCoin''(bytes);
$IsValid'vec'$1_aptos_coin_AptosCoin''($$res)));

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
function  $1_from_bcs_deserialize'$1_option_Option'u64''(bytes: Vec (int)): $1_option_Option'u64';
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserialize'$1_option_Option'u64''(bytes);
$IsValid'$1_option_Option'u64''($$res)));

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:7:9+41
function  $1_from_bcs_deserialize'$1_option_Option'u128''(bytes: Vec (int)): $1_option_Option'u128';
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserialize'$1_option_Option'u128''(bytes);
$IsValid'$1_option_Option'u128''($$res)));

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
function  $1_from_bcs_deserialize'$1_event_EventHandle'$1_reconfiguration_NewEpochEvent''(bytes: Vec (int)): $1_event_EventHandle'$1_reconfiguration_NewEpochEvent';
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserialize'$1_event_EventHandle'$1_reconfiguration_NewEpochEvent''(bytes);
$IsValid'$1_event_EventHandle'$1_reconfiguration_NewEpochEvent''($$res)));

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:7:9+41
function  $1_from_bcs_deserialize'$1_event_EventHandle'$1_aptos_governance_CreateProposalEvent''(bytes: Vec (int)): $1_event_EventHandle'$1_aptos_governance_CreateProposalEvent';
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserialize'$1_event_EventHandle'$1_aptos_governance_CreateProposalEvent''(bytes);
$IsValid'$1_event_EventHandle'$1_aptos_governance_CreateProposalEvent''($$res)));

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:7:9+41
function  $1_from_bcs_deserialize'$1_event_EventHandle'$1_aptos_governance_VoteEvent''(bytes: Vec (int)): $1_event_EventHandle'$1_aptos_governance_VoteEvent';
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserialize'$1_event_EventHandle'$1_aptos_governance_VoteEvent''(bytes);
$IsValid'$1_event_EventHandle'$1_aptos_governance_VoteEvent''($$res)));

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:7:9+41
function  $1_from_bcs_deserialize'$1_event_EventHandle'$1_aptos_governance_UpdateConfigEvent''(bytes: Vec (int)): $1_event_EventHandle'$1_aptos_governance_UpdateConfigEvent';
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserialize'$1_event_EventHandle'$1_aptos_governance_UpdateConfigEvent''(bytes);
$IsValid'$1_event_EventHandle'$1_aptos_governance_UpdateConfigEvent''($$res)));

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
function  $1_from_bcs_deserialize'$1_coin_BurnCapability'$1_aptos_coin_AptosCoin''(bytes: Vec (int)): $1_coin_BurnCapability'$1_aptos_coin_AptosCoin';
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserialize'$1_coin_BurnCapability'$1_aptos_coin_AptosCoin''(bytes);
$IsValid'$1_coin_BurnCapability'$1_aptos_coin_AptosCoin''($$res)));

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
function  $1_from_bcs_deserialize'$1_coin_MintCapability'$1_aptos_coin_AptosCoin''(bytes: Vec (int)): $1_coin_MintCapability'$1_aptos_coin_AptosCoin';
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserialize'$1_coin_MintCapability'$1_aptos_coin_AptosCoin''(bytes);
$IsValid'$1_coin_MintCapability'$1_aptos_coin_AptosCoin''($$res)));

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:7:9+41
function  $1_from_bcs_deserialize'$1_aptos_coin_AptosCoin'(bytes: Vec (int)): $1_aptos_coin_AptosCoin;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserialize'$1_aptos_coin_AptosCoin'(bytes);
$IsValid'$1_aptos_coin_AptosCoin'($$res)));

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
function  $1_from_bcs_deserialize'$1_simple_map_SimpleMap'$1_string_String_vec'u8'''(bytes: Vec (int)): Table int (Vec (int));
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserialize'$1_simple_map_SimpleMap'$1_string_String_vec'u8'''(bytes);
$IsValid'$1_simple_map_SimpleMap'$1_string_String_vec'u8'''($$res)));

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:7:9+41
function  $1_from_bcs_deserialize'$1_voting_CreateProposalEvent'(bytes: Vec (int)): $1_voting_CreateProposalEvent;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserialize'$1_voting_CreateProposalEvent'(bytes);
$IsValid'$1_voting_CreateProposalEvent'($$res)));

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:7:9+41
function  $1_from_bcs_deserialize'$1_voting_Proposal'$1_governance_proposal_GovernanceProposal''(bytes: Vec (int)): $1_voting_Proposal'$1_governance_proposal_GovernanceProposal';
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserialize'$1_voting_Proposal'$1_governance_proposal_GovernanceProposal''(bytes);
$IsValid'$1_voting_Proposal'$1_governance_proposal_GovernanceProposal''($$res)));

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
function  $1_from_bcs_deserialize'$1_stake_ValidatorInfo'(bytes: Vec (int)): $1_stake_ValidatorInfo;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserialize'$1_stake_ValidatorInfo'(bytes);
$IsValid'$1_stake_ValidatorInfo'($$res)));

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
function  $1_from_bcs_deserialize'$1_aptos_governance_CreateProposalEvent'(bytes: Vec (int)): $1_aptos_governance_CreateProposalEvent;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserialize'$1_aptos_governance_CreateProposalEvent'(bytes);
$IsValid'$1_aptos_governance_CreateProposalEvent'($$res)));

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:7:9+41
function  $1_from_bcs_deserialize'$1_aptos_governance_GovernanceConfig'(bytes: Vec (int)): $1_aptos_governance_GovernanceConfig;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserialize'$1_aptos_governance_GovernanceConfig'(bytes);
$IsValid'$1_aptos_governance_GovernanceConfig'($$res)));

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:7:9+41
function  $1_from_bcs_deserialize'$1_aptos_governance_GovernanceEvents'(bytes: Vec (int)): $1_aptos_governance_GovernanceEvents;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserialize'$1_aptos_governance_GovernanceEvents'(bytes);
$IsValid'$1_aptos_governance_GovernanceEvents'($$res)));

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
function  $1_from_bcs_deserializable'vec'$1_aptos_coin_AptosCoin''(bytes: Vec (int)): bool;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserializable'vec'$1_aptos_coin_AptosCoin''(bytes);
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
function  $1_from_bcs_deserializable'$1_option_Option'u64''(bytes: Vec (int)): bool;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserializable'$1_option_Option'u64''(bytes);
$IsValid'bool'($$res)));

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:11:9+47
function  $1_from_bcs_deserializable'$1_option_Option'u128''(bytes: Vec (int)): bool;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserializable'$1_option_Option'u128''(bytes);
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
function  $1_from_bcs_deserializable'$1_event_EventHandle'$1_reconfiguration_NewEpochEvent''(bytes: Vec (int)): bool;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserializable'$1_event_EventHandle'$1_reconfiguration_NewEpochEvent''(bytes);
$IsValid'bool'($$res)));

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:11:9+47
function  $1_from_bcs_deserializable'$1_event_EventHandle'$1_aptos_governance_CreateProposalEvent''(bytes: Vec (int)): bool;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserializable'$1_event_EventHandle'$1_aptos_governance_CreateProposalEvent''(bytes);
$IsValid'bool'($$res)));

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:11:9+47
function  $1_from_bcs_deserializable'$1_event_EventHandle'$1_aptos_governance_VoteEvent''(bytes: Vec (int)): bool;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserializable'$1_event_EventHandle'$1_aptos_governance_VoteEvent''(bytes);
$IsValid'bool'($$res)));

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:11:9+47
function  $1_from_bcs_deserializable'$1_event_EventHandle'$1_aptos_governance_UpdateConfigEvent''(bytes: Vec (int)): bool;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserializable'$1_event_EventHandle'$1_aptos_governance_UpdateConfigEvent''(bytes);
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
function  $1_from_bcs_deserializable'$1_coin_BurnCapability'$1_aptos_coin_AptosCoin''(bytes: Vec (int)): bool;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserializable'$1_coin_BurnCapability'$1_aptos_coin_AptosCoin''(bytes);
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
function  $1_from_bcs_deserializable'$1_coin_MintCapability'$1_aptos_coin_AptosCoin''(bytes: Vec (int)): bool;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserializable'$1_coin_MintCapability'$1_aptos_coin_AptosCoin''(bytes);
$IsValid'bool'($$res)));

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:11:9+47
function  $1_from_bcs_deserializable'$1_aptos_coin_AptosCoin'(bytes: Vec (int)): bool;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserializable'$1_aptos_coin_AptosCoin'(bytes);
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
function  $1_from_bcs_deserializable'$1_simple_map_SimpleMap'$1_string_String_vec'u8'''(bytes: Vec (int)): bool;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserializable'$1_simple_map_SimpleMap'$1_string_String_vec'u8'''(bytes);
$IsValid'bool'($$res)));

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:11:9+47
function  $1_from_bcs_deserializable'$1_voting_CreateProposalEvent'(bytes: Vec (int)): bool;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserializable'$1_voting_CreateProposalEvent'(bytes);
$IsValid'bool'($$res)));

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:11:9+47
function  $1_from_bcs_deserializable'$1_voting_Proposal'$1_governance_proposal_GovernanceProposal''(bytes: Vec (int)): bool;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserializable'$1_voting_Proposal'$1_governance_proposal_GovernanceProposal''(bytes);
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
function  $1_from_bcs_deserializable'$1_stake_ValidatorInfo'(bytes: Vec (int)): bool;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserializable'$1_stake_ValidatorInfo'(bytes);
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
function  $1_from_bcs_deserializable'$1_aptos_governance_CreateProposalEvent'(bytes: Vec (int)): bool;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserializable'$1_aptos_governance_CreateProposalEvent'(bytes);
$IsValid'bool'($$res)));

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:11:9+47
function  $1_from_bcs_deserializable'$1_aptos_governance_GovernanceConfig'(bytes: Vec (int)): bool;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserializable'$1_aptos_governance_GovernanceConfig'(bytes);
$IsValid'bool'($$res)));

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:11:9+47
function  $1_from_bcs_deserializable'$1_aptos_governance_GovernanceEvents'(bytes: Vec (int)): bool;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserializable'$1_aptos_governance_GovernanceEvents'(bytes);
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

// struct event::EventHandle<aptos_governance::CreateProposalEvent> at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/event.move:16:5+224
type {:datatype} $1_event_EventHandle'$1_aptos_governance_CreateProposalEvent';
function {:constructor} $1_event_EventHandle'$1_aptos_governance_CreateProposalEvent'($counter: int, $guid: $1_guid_GUID): $1_event_EventHandle'$1_aptos_governance_CreateProposalEvent';
function {:inline} $Update'$1_event_EventHandle'$1_aptos_governance_CreateProposalEvent''_counter(s: $1_event_EventHandle'$1_aptos_governance_CreateProposalEvent', x: int): $1_event_EventHandle'$1_aptos_governance_CreateProposalEvent' {
    $1_event_EventHandle'$1_aptos_governance_CreateProposalEvent'(x, $guid#$1_event_EventHandle'$1_aptos_governance_CreateProposalEvent'(s))
}
function {:inline} $Update'$1_event_EventHandle'$1_aptos_governance_CreateProposalEvent''_guid(s: $1_event_EventHandle'$1_aptos_governance_CreateProposalEvent', x: $1_guid_GUID): $1_event_EventHandle'$1_aptos_governance_CreateProposalEvent' {
    $1_event_EventHandle'$1_aptos_governance_CreateProposalEvent'($counter#$1_event_EventHandle'$1_aptos_governance_CreateProposalEvent'(s), x)
}
function $IsValid'$1_event_EventHandle'$1_aptos_governance_CreateProposalEvent''(s: $1_event_EventHandle'$1_aptos_governance_CreateProposalEvent'): bool {
    $IsValid'u64'($counter#$1_event_EventHandle'$1_aptos_governance_CreateProposalEvent'(s))
      && $IsValid'$1_guid_GUID'($guid#$1_event_EventHandle'$1_aptos_governance_CreateProposalEvent'(s))
}
function {:inline} $IsEqual'$1_event_EventHandle'$1_aptos_governance_CreateProposalEvent''(s1: $1_event_EventHandle'$1_aptos_governance_CreateProposalEvent', s2: $1_event_EventHandle'$1_aptos_governance_CreateProposalEvent'): bool {
    s1 == s2
}

// struct event::EventHandle<aptos_governance::VoteEvent> at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/event.move:16:5+224
type {:datatype} $1_event_EventHandle'$1_aptos_governance_VoteEvent';
function {:constructor} $1_event_EventHandle'$1_aptos_governance_VoteEvent'($counter: int, $guid: $1_guid_GUID): $1_event_EventHandle'$1_aptos_governance_VoteEvent';
function {:inline} $Update'$1_event_EventHandle'$1_aptos_governance_VoteEvent''_counter(s: $1_event_EventHandle'$1_aptos_governance_VoteEvent', x: int): $1_event_EventHandle'$1_aptos_governance_VoteEvent' {
    $1_event_EventHandle'$1_aptos_governance_VoteEvent'(x, $guid#$1_event_EventHandle'$1_aptos_governance_VoteEvent'(s))
}
function {:inline} $Update'$1_event_EventHandle'$1_aptos_governance_VoteEvent''_guid(s: $1_event_EventHandle'$1_aptos_governance_VoteEvent', x: $1_guid_GUID): $1_event_EventHandle'$1_aptos_governance_VoteEvent' {
    $1_event_EventHandle'$1_aptos_governance_VoteEvent'($counter#$1_event_EventHandle'$1_aptos_governance_VoteEvent'(s), x)
}
function $IsValid'$1_event_EventHandle'$1_aptos_governance_VoteEvent''(s: $1_event_EventHandle'$1_aptos_governance_VoteEvent'): bool {
    $IsValid'u64'($counter#$1_event_EventHandle'$1_aptos_governance_VoteEvent'(s))
      && $IsValid'$1_guid_GUID'($guid#$1_event_EventHandle'$1_aptos_governance_VoteEvent'(s))
}
function {:inline} $IsEqual'$1_event_EventHandle'$1_aptos_governance_VoteEvent''(s1: $1_event_EventHandle'$1_aptos_governance_VoteEvent', s2: $1_event_EventHandle'$1_aptos_governance_VoteEvent'): bool {
    s1 == s2
}

// struct event::EventHandle<aptos_governance::UpdateConfigEvent> at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/event.move:16:5+224
type {:datatype} $1_event_EventHandle'$1_aptos_governance_UpdateConfigEvent';
function {:constructor} $1_event_EventHandle'$1_aptos_governance_UpdateConfigEvent'($counter: int, $guid: $1_guid_GUID): $1_event_EventHandle'$1_aptos_governance_UpdateConfigEvent';
function {:inline} $Update'$1_event_EventHandle'$1_aptos_governance_UpdateConfigEvent''_counter(s: $1_event_EventHandle'$1_aptos_governance_UpdateConfigEvent', x: int): $1_event_EventHandle'$1_aptos_governance_UpdateConfigEvent' {
    $1_event_EventHandle'$1_aptos_governance_UpdateConfigEvent'(x, $guid#$1_event_EventHandle'$1_aptos_governance_UpdateConfigEvent'(s))
}
function {:inline} $Update'$1_event_EventHandle'$1_aptos_governance_UpdateConfigEvent''_guid(s: $1_event_EventHandle'$1_aptos_governance_UpdateConfigEvent', x: $1_guid_GUID): $1_event_EventHandle'$1_aptos_governance_UpdateConfigEvent' {
    $1_event_EventHandle'$1_aptos_governance_UpdateConfigEvent'($counter#$1_event_EventHandle'$1_aptos_governance_UpdateConfigEvent'(s), x)
}
function $IsValid'$1_event_EventHandle'$1_aptos_governance_UpdateConfigEvent''(s: $1_event_EventHandle'$1_aptos_governance_UpdateConfigEvent'): bool {
    $IsValid'u64'($counter#$1_event_EventHandle'$1_aptos_governance_UpdateConfigEvent'(s))
      && $IsValid'$1_guid_GUID'($guid#$1_event_EventHandle'$1_aptos_governance_UpdateConfigEvent'(s))
}
function {:inline} $IsEqual'$1_event_EventHandle'$1_aptos_governance_UpdateConfigEvent''(s1: $1_event_EventHandle'$1_aptos_governance_UpdateConfigEvent', s2: $1_event_EventHandle'$1_aptos_governance_UpdateConfigEvent'): bool {
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

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aggregator/optional_aggregator.move:190:5+141
function {:inline} $1_optional_aggregator_$is_parallelizable(optional_aggregator: $1_optional_aggregator_OptionalAggregator): bool {
    $1_option_$is_some'$1_aggregator_Aggregator'($aggregator#$1_optional_aggregator_OptionalAggregator(optional_aggregator))
}

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aggregator/optional_aggregator.spec.move:134:10+323
function {:inline} $1_optional_aggregator_optional_aggregator_value(optional_aggregator: $1_optional_aggregator_OptionalAggregator): int {
    (if ($1_optional_aggregator_$is_parallelizable(optional_aggregator)) then ($1_aggregator_spec_aggregator_get_val($1_option_$borrow'$1_aggregator_Aggregator'($aggregator#$1_optional_aggregator_OptionalAggregator(optional_aggregator)))) else ($value#$1_optional_aggregator_Integer($1_option_$borrow'$1_optional_aggregator_Integer'($integer#$1_optional_aggregator_OptionalAggregator(optional_aggregator)))))
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

// fun optional_aggregator::read [baseline] at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aggregator/optional_aggregator.move:179:5+387
procedure {:inline 1} $1_optional_aggregator_read(_$t0: $1_optional_aggregator_OptionalAggregator) returns ($ret0: int)
{
    // declare local variables
    var $t1: int;
    var $t2: $1_option_Option'$1_aggregator_Aggregator';
    var $t3: bool;
    var $t4: $1_option_Option'$1_aggregator_Aggregator';
    var $t5: $1_aggregator_Aggregator;
    var $t6: bool;
    var $t7: int;
    var $t8: $1_option_Option'$1_optional_aggregator_Integer';
    var $t9: $1_optional_aggregator_Integer;
    var $t10: bool;
    var $t0: $1_optional_aggregator_OptionalAggregator;
    var $temp_0'$1_optional_aggregator_OptionalAggregator': $1_optional_aggregator_OptionalAggregator;
    var $temp_0'u128': int;
    $t0 := _$t0;

    // bytecode translation starts here
    // trace_local[optional_aggregator]($t0) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aggregator/optional_aggregator.move:179:5+1
    assume {:print "$at(78,6823,6824)"} true;
    assume {:print "$track_local(22,10,0):", $t0} $t0 == $t0;

    // $t2 := get_field<optional_aggregator::OptionalAggregator>.aggregator($t0) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aggregator/optional_aggregator.move:180:29+31
    assume {:print "$at(78,6917,6948)"} true;
    $t2 := $aggregator#$1_optional_aggregator_OptionalAggregator($t0);

    // $t3 := opaque begin: option::is_some<aggregator::Aggregator>($t2) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aggregator/optional_aggregator.move:180:13+48

    // assume WellFormed($t3) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aggregator/optional_aggregator.move:180:13+48
    assume $IsValid'bool'($t3);

    // assume Eq<bool>($t3, option::spec_is_some<aggregator::Aggregator>($t2)) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aggregator/optional_aggregator.move:180:13+48
    assume $IsEqual'bool'($t3, $1_option_spec_is_some'$1_aggregator_Aggregator'($t2));

    // $t3 := opaque end: option::is_some<aggregator::Aggregator>($t2) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aggregator/optional_aggregator.move:180:13+48

    // if ($t3) goto L1 else goto L0 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aggregator/optional_aggregator.move:180:9+307
    if ($t3) { goto L1; } else { goto L0; }

    // label L1 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aggregator/optional_aggregator.move:181:46+19
    assume {:print "$at(78,6998,7017)"} true;
L1:

    // $t4 := get_field<optional_aggregator::OptionalAggregator>.aggregator($t0) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aggregator/optional_aggregator.move:181:45+31
    assume {:print "$at(78,6997,7028)"} true;
    $t4 := $aggregator#$1_optional_aggregator_OptionalAggregator($t0);

    // $t5 := opaque begin: option::borrow<aggregator::Aggregator>($t4) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aggregator/optional_aggregator.move:181:30+47

    // assume Identical($t6, option::spec_is_none<aggregator::Aggregator>($t4)) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aggregator/optional_aggregator.move:181:30+47
    assume ($t6 == $1_option_spec_is_none'$1_aggregator_Aggregator'($t4));

    // if ($t6) goto L6 else goto L5 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aggregator/optional_aggregator.move:181:30+47
    if ($t6) { goto L6; } else { goto L5; }

    // label L6 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aggregator/optional_aggregator.move:181:30+47
L6:

    // assume And(option::spec_is_none<aggregator::Aggregator>($t4), Eq(262145, $t7)) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aggregator/optional_aggregator.move:181:30+47
    assume {:print "$at(78,6982,7029)"} true;
    assume ($1_option_spec_is_none'$1_aggregator_Aggregator'($t4) && $IsEqual'num'(262145, $t7));

    // trace_abort($t7) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aggregator/optional_aggregator.move:181:30+47
    assume {:print "$at(78,6982,7029)"} true;
    assume {:print "$track_abort(22,10):", $t7} $t7 == $t7;

    // goto L4 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aggregator/optional_aggregator.move:181:30+47
    goto L4;

    // label L5 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aggregator/optional_aggregator.move:181:30+47
L5:

    // assume WellFormed($t5) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aggregator/optional_aggregator.move:181:30+47
    assume {:print "$at(78,6982,7029)"} true;
    assume $IsValid'$1_aggregator_Aggregator'($t5);

    // assume Eq<aggregator::Aggregator>($t5, option::spec_borrow<aggregator::Aggregator>($t4)) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aggregator/optional_aggregator.move:181:30+47
    assume $IsEqual'$1_aggregator_Aggregator'($t5, $1_option_spec_borrow'$1_aggregator_Aggregator'($t4));

    // $t5 := opaque end: option::borrow<aggregator::Aggregator>($t4) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aggregator/optional_aggregator.move:181:30+47

    // $t1 := opaque begin: aggregator::read($t5) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aggregator/optional_aggregator.move:182:13+28
    assume {:print "$at(78,7043,7071)"} true;

    // assume WellFormed($t1) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aggregator/optional_aggregator.move:182:13+28
    assume $IsValid'u128'($t1);

    // assume Eq<u128>($t1, aggregator::spec_read($t5)) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aggregator/optional_aggregator.move:182:13+28
    assume $IsEqual'u128'($t1, $1_aggregator_spec_read($t5));

    // assume Le($t1, aggregator::spec_get_limit($t5)) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aggregator/optional_aggregator.move:182:13+28
    assume ($t1 <= $1_aggregator_spec_get_limit($t5));

    // $t1 := opaque end: aggregator::read($t5) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aggregator/optional_aggregator.move:182:13+28

    // goto L2 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aggregator/optional_aggregator.move:180:9+307
    assume {:print "$at(78,6897,7204)"} true;
    goto L2;

    // label L0 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aggregator/optional_aggregator.move:184:43+19
    assume {:print "$at(78,7131,7150)"} true;
L0:

    // $t8 := get_field<optional_aggregator::OptionalAggregator>.integer($t0) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aggregator/optional_aggregator.move:184:42+28
    assume {:print "$at(78,7130,7158)"} true;
    $t8 := $integer#$1_optional_aggregator_OptionalAggregator($t0);

    // $t9 := opaque begin: option::borrow<optional_aggregator::Integer>($t8) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aggregator/optional_aggregator.move:184:27+44

    // assume Identical($t10, option::spec_is_none<optional_aggregator::Integer>($t8)) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aggregator/optional_aggregator.move:184:27+44
    assume ($t10 == $1_option_spec_is_none'$1_optional_aggregator_Integer'($t8));

    // if ($t10) goto L8 else goto L7 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aggregator/optional_aggregator.move:184:27+44
    if ($t10) { goto L8; } else { goto L7; }

    // label L8 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aggregator/optional_aggregator.move:184:27+44
L8:

    // assume And(option::spec_is_none<optional_aggregator::Integer>($t8), Eq(262145, $t7)) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aggregator/optional_aggregator.move:184:27+44
    assume {:print "$at(78,7115,7159)"} true;
    assume ($1_option_spec_is_none'$1_optional_aggregator_Integer'($t8) && $IsEqual'num'(262145, $t7));

    // trace_abort($t7) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aggregator/optional_aggregator.move:184:27+44
    assume {:print "$at(78,7115,7159)"} true;
    assume {:print "$track_abort(22,10):", $t7} $t7 == $t7;

    // goto L4 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aggregator/optional_aggregator.move:184:27+44
    goto L4;

    // label L7 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aggregator/optional_aggregator.move:184:27+44
L7:

    // assume WellFormed($t9) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aggregator/optional_aggregator.move:184:27+44
    assume {:print "$at(78,7115,7159)"} true;
    assume $IsValid'$1_optional_aggregator_Integer'($t9);

    // assume Eq<optional_aggregator::Integer>($t9, option::spec_borrow<optional_aggregator::Integer>($t8)) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aggregator/optional_aggregator.move:184:27+44
    assume $IsEqual'$1_optional_aggregator_Integer'($t9, $1_option_spec_borrow'$1_optional_aggregator_Integer'($t8));

    // $t9 := opaque end: option::borrow<optional_aggregator::Integer>($t8) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aggregator/optional_aggregator.move:184:27+44

    // $t1 := optional_aggregator::read_integer($t9) on_abort goto L4 with $t7 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aggregator/optional_aggregator.move:185:13+21
    assume {:print "$at(78,7173,7194)"} true;
    call $t1 := $1_optional_aggregator_read_integer($t9);
    if ($abort_flag) {
        assume {:print "$at(78,7173,7194)"} true;
        $t7 := $abort_code;
        assume {:print "$track_abort(22,10):", $t7} $t7 == $t7;
        goto L4;
    }

    // label L2 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aggregator/optional_aggregator.move:180:9+307
    assume {:print "$at(78,6897,7204)"} true;
L2:

    // trace_return[0]($t1) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aggregator/optional_aggregator.move:180:9+307
    assume {:print "$at(78,6897,7204)"} true;
    assume {:print "$track_return(22,10,0):", $t1} $t1 == $t1;

    // label L3 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aggregator/optional_aggregator.move:187:5+1
    assume {:print "$at(78,7209,7210)"} true;
L3:

    // return $t1 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aggregator/optional_aggregator.move:187:5+1
    assume {:print "$at(78,7209,7210)"} true;
    $ret0 := $t1;
    return;

    // label L4 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aggregator/optional_aggregator.move:187:5+1
L4:

    // abort($t7) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aggregator/optional_aggregator.move:187:5+1
    assume {:print "$at(78,7209,7210)"} true;
    $abort_code := $t7;
    $abort_flag := true;
    return;

}

// fun optional_aggregator::read_integer [baseline] at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aggregator/optional_aggregator.move:54:5+71
procedure {:inline 1} $1_optional_aggregator_read_integer(_$t0: $1_optional_aggregator_Integer) returns ($ret0: int)
{
    // declare local variables
    var $t1: int;
    var $t0: $1_optional_aggregator_Integer;
    var $temp_0'$1_optional_aggregator_Integer': $1_optional_aggregator_Integer;
    var $temp_0'u128': int;
    $t0 := _$t0;

    // bytecode translation starts here
    // trace_local[integer]($t0) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aggregator/optional_aggregator.move:54:5+1
    assume {:print "$at(78,1785,1786)"} true;
    assume {:print "$track_local(22,11,0):", $t0} $t0 == $t0;

    // $t1 := get_field<optional_aggregator::Integer>.value($t0) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aggregator/optional_aggregator.move:55:9+13
    assume {:print "$at(78,1837,1850)"} true;
    $t1 := $value#$1_optional_aggregator_Integer($t0);

    // trace_return[0]($t1) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aggregator/optional_aggregator.move:55:9+13
    assume {:print "$track_return(22,11,0):", $t1} $t1 == $t1;

    // label L1 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aggregator/optional_aggregator.move:56:5+1
    assume {:print "$at(78,1855,1856)"} true;
L1:

    // return $t1 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aggregator/optional_aggregator.move:56:5+1
    assume {:print "$at(78,1855,1856)"} true;
    $ret0 := $t1;
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

// fun coin::value<aptos_coin::AptosCoin> [baseline] at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.move:527:5+81
procedure {:inline 1} $1_coin_value'$1_aptos_coin_AptosCoin'(_$t0: $1_coin_Coin'$1_aptos_coin_AptosCoin') returns ($ret0: int)
{
    // declare local variables
    var $t1: int;
    var $t0: $1_coin_Coin'$1_aptos_coin_AptosCoin';
    var $temp_0'$1_coin_Coin'$1_aptos_coin_AptosCoin'': $1_coin_Coin'$1_aptos_coin_AptosCoin';
    var $temp_0'u64': int;
    $t0 := _$t0;

    // bytecode translation starts here
    // trace_local[coin]($t0) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.move:527:5+1
    assume {:print "$at(92,20291,20292)"} true;
    assume {:print "$track_local(23,34,0):", $t0} $t0 == $t0;

    // $t1 := get_field<coin::Coin<#0>>.value($t0) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.move:528:9+10
    assume {:print "$at(92,20356,20366)"} true;
    $t1 := $value#$1_coin_Coin'$1_aptos_coin_AptosCoin'($t0);

    // trace_return[0]($t1) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.move:528:9+10
    assume {:print "$track_return(23,34,0):", $t1} $t1 == $t1;

    // label L1 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.move:529:5+1
    assume {:print "$at(92,20371,20372)"} true;
L1:

    // return $t1 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.move:529:5+1
    assume {:print "$at(92,20371,20372)"} true;
    $ret0 := $t1;
    return;

}

// fun coin::supply<aptos_coin::AptosCoin> [baseline] at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.move:270:5+489
procedure {:inline 1} $1_coin_supply'$1_aptos_coin_AptosCoin'() returns ($ret0: $1_option_Option'u128')
{
    // declare local variables
    var $t0: $1_option_Option'u128';
    var $t1: $1_option_Option'$1_optional_aggregator_OptionalAggregator';
    var $t2: int;
    var $t3: $1_option_Option'$1_optional_aggregator_OptionalAggregator';
    var $t4: $1_optional_aggregator_OptionalAggregator;
    var $t5: int;
    var $t6: int;
    var $t7: $1_coin_CoinInfo'$1_aptos_coin_AptosCoin';
    var $t8: int;
    var $t9: $1_option_Option'$1_optional_aggregator_OptionalAggregator';
    var $t10: bool;
    var $t11: $1_optional_aggregator_OptionalAggregator;
    var $t12: bool;
    var $t13: int;
    var $temp_0'$1_option_Option'$1_optional_aggregator_OptionalAggregator'': $1_option_Option'$1_optional_aggregator_OptionalAggregator';
    var $temp_0'$1_option_Option'u128'': $1_option_Option'u128';

    // bytecode translation starts here
    // assume Identical($t2, select type_info::TypeInfo.account_address(type_info::$type_of<#0>())) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.spec.move:91:9+63
    assume {:print "$at(93,3461,3524)"} true;
    assume ($t2 == $account_address#$1_type_info_TypeInfo($1_type_info_TypeInfo(1, Vec(DefaultVecMap()[0 := 97][1 := 112][2 := 116][3 := 111][4 := 115][5 := 95][6 := 99][7 := 111][8 := 105][9 := 110], 10), Vec(DefaultVecMap()[0 := 65][1 := 112][2 := 116][3 := 111][4 := 115][5 := 67][6 := 111][7 := 105][8 := 110], 9))));

    // assume Identical($t3, select coin::CoinInfo.supply(global<coin::CoinInfo<#0>>($t2))) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.spec.move:93:9+64
    assume {:print "$at(93,3591,3655)"} true;
    assume ($t3 == $supply#$1_coin_CoinInfo'$1_aptos_coin_AptosCoin'($ResourceValue($1_coin_CoinInfo'$1_aptos_coin_AptosCoin'_$memory, $t2)));

    // assume Identical($t4, option::spec_borrow<optional_aggregator::OptionalAggregator>($t3)) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.spec.move:94:9+47
    assume {:print "$at(93,3664,3711)"} true;
    assume ($t4 == $1_option_spec_borrow'$1_optional_aggregator_OptionalAggregator'($t3));

    // assume Identical($t5, optional_aggregator::optional_aggregator_value($t4)) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.spec.move:95:9+67
    assume {:print "$at(93,3720,3787)"} true;
    assume ($t5 == $1_optional_aggregator_optional_aggregator_value($t4));

    // $t6 := opaque begin: coin::coin_address<#0>() at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.move:271:63+24
    assume {:print "$at(92,10080,10104)"} true;

    // assume WellFormed($t6) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.move:271:63+24
    assume $IsValid'address'($t6);

    // assume Eq<address>($t6, select type_info::TypeInfo.account_address(type_info::$type_of<#0>())) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.move:271:63+24
    assume $IsEqual'address'($t6, $account_address#$1_type_info_TypeInfo($1_type_info_TypeInfo(1, Vec(DefaultVecMap()[0 := 97][1 := 112][2 := 116][3 := 111][4 := 115][5 := 95][6 := 99][7 := 111][8 := 105][9 := 110], 10), Vec(DefaultVecMap()[0 := 65][1 := 112][2 := 116][3 := 111][4 := 115][5 := 67][6 := 111][7 := 105][8 := 110], 9))));

    // $t6 := opaque end: coin::coin_address<#0>() at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.move:271:63+24

    // $t7 := get_global<coin::CoinInfo<#0>>($t6) on_abort goto L4 with $t8 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.move:271:29+13
    if (!$ResourceExists($1_coin_CoinInfo'$1_aptos_coin_AptosCoin'_$memory, $t6)) {
        call $ExecFailureAbort();
    } else {
        $t7 := $ResourceValue($1_coin_CoinInfo'$1_aptos_coin_AptosCoin'_$memory, $t6);
    }
    if ($abort_flag) {
        assume {:print "$at(92,10046,10059)"} true;
        $t8 := $abort_code;
        assume {:print "$track_abort(23,29):", $t8} $t8 == $t8;
        goto L4;
    }

    // $t9 := get_field<coin::CoinInfo<#0>>.supply($t7) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.move:271:28+67
    $t9 := $supply#$1_coin_CoinInfo'$1_aptos_coin_AptosCoin'($t7);

    // trace_local[maybe_supply]($t9) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.move:271:13+12
    assume {:print "$track_local(23,29,1):", $t9} $t9 == $t9;

    // $t10 := opaque begin: option::is_some<optional_aggregator::OptionalAggregator>($t9) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.move:272:13+29
    assume {:print "$at(92,10126,10155)"} true;

    // assume WellFormed($t10) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.move:272:13+29
    assume $IsValid'bool'($t10);

    // assume Eq<bool>($t10, option::spec_is_some<optional_aggregator::OptionalAggregator>($t9)) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.move:272:13+29
    assume $IsEqual'bool'($t10, $1_option_spec_is_some'$1_optional_aggregator_OptionalAggregator'($t9));

    // $t10 := opaque end: option::is_some<optional_aggregator::OptionalAggregator>($t9) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.move:272:13+29

    // if ($t10) goto L1 else goto L0 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.move:272:9+315
    if ($t10) { goto L1; } else { goto L0; }

    // label L1 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.move:274:41+12
    assume {:print "$at(92,10278,10290)"} true;
L1:

    // $t11 := opaque begin: option::borrow<optional_aggregator::OptionalAggregator>($t9) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.move:274:26+28
    assume {:print "$at(92,10263,10291)"} true;

    // assume Identical($t12, option::spec_is_none<optional_aggregator::OptionalAggregator>($t9)) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.move:274:26+28
    assume ($t12 == $1_option_spec_is_none'$1_optional_aggregator_OptionalAggregator'($t9));

    // if ($t12) goto L6 else goto L5 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.move:274:26+28
    if ($t12) { goto L6; } else { goto L5; }

    // label L6 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.move:274:26+28
L6:

    // assume And(option::spec_is_none<optional_aggregator::OptionalAggregator>($t9), Eq(262145, $t8)) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.move:274:26+28
    assume {:print "$at(92,10263,10291)"} true;
    assume ($1_option_spec_is_none'$1_optional_aggregator_OptionalAggregator'($t9) && $IsEqual'num'(262145, $t8));

    // trace_abort($t8) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.move:274:26+28
    assume {:print "$at(92,10263,10291)"} true;
    assume {:print "$track_abort(23,29):", $t8} $t8 == $t8;

    // goto L4 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.move:274:26+28
    goto L4;

    // label L5 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.move:274:26+28
L5:

    // assume And(WellFormed($t11), And(And(And(And(And(Iff(option::$is_some<aggregator::Aggregator>(select optional_aggregator::OptionalAggregator.aggregator($t11)), option::$is_none<optional_aggregator::Integer>(select optional_aggregator::OptionalAggregator.integer($t11))), Iff(option::$is_some<optional_aggregator::Integer>(select optional_aggregator::OptionalAggregator.integer($t11)), option::$is_none<aggregator::Aggregator>(select optional_aggregator::OptionalAggregator.aggregator($t11)))), Implies(option::$is_some<optional_aggregator::Integer>(select optional_aggregator::OptionalAggregator.integer($t11)), Le(select optional_aggregator::Integer.value(option::$borrow<optional_aggregator::Integer>(select optional_aggregator::OptionalAggregator.integer($t11))), select optional_aggregator::Integer.limit(option::$borrow<optional_aggregator::Integer>(select optional_aggregator::OptionalAggregator.integer($t11)))))), Implies(option::$is_some<aggregator::Aggregator>(select optional_aggregator::OptionalAggregator.aggregator($t11)), Le(aggregator::spec_aggregator_get_val(option::$borrow<aggregator::Aggregator>(select optional_aggregator::OptionalAggregator.aggregator($t11))), aggregator::spec_get_limit(option::$borrow<aggregator::Aggregator>(select optional_aggregator::OptionalAggregator.aggregator($t11)))))), Le(Len<aggregator::Aggregator>(select option::Option.vec(select optional_aggregator::OptionalAggregator.aggregator($t11))), 1)), Le(Len<optional_aggregator::Integer>(select option::Option.vec(select optional_aggregator::OptionalAggregator.integer($t11))), 1))) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.move:274:26+28
    assume {:print "$at(92,10263,10291)"} true;
    assume ($IsValid'$1_optional_aggregator_OptionalAggregator'($t11) && (((((($1_option_$is_some'$1_aggregator_Aggregator'($aggregator#$1_optional_aggregator_OptionalAggregator($t11)) <==> $1_option_$is_none'$1_optional_aggregator_Integer'($integer#$1_optional_aggregator_OptionalAggregator($t11))) && ($1_option_$is_some'$1_optional_aggregator_Integer'($integer#$1_optional_aggregator_OptionalAggregator($t11)) <==> $1_option_$is_none'$1_aggregator_Aggregator'($aggregator#$1_optional_aggregator_OptionalAggregator($t11)))) && ($1_option_$is_some'$1_optional_aggregator_Integer'($integer#$1_optional_aggregator_OptionalAggregator($t11)) ==> ($value#$1_optional_aggregator_Integer($1_option_$borrow'$1_optional_aggregator_Integer'($integer#$1_optional_aggregator_OptionalAggregator($t11))) <= $limit#$1_optional_aggregator_Integer($1_option_$borrow'$1_optional_aggregator_Integer'($integer#$1_optional_aggregator_OptionalAggregator($t11)))))) && ($1_option_$is_some'$1_aggregator_Aggregator'($aggregator#$1_optional_aggregator_OptionalAggregator($t11)) ==> ($1_aggregator_spec_aggregator_get_val($1_option_$borrow'$1_aggregator_Aggregator'($aggregator#$1_optional_aggregator_OptionalAggregator($t11))) <= $1_aggregator_spec_get_limit($1_option_$borrow'$1_aggregator_Aggregator'($aggregator#$1_optional_aggregator_OptionalAggregator($t11)))))) && (LenVec($vec#$1_option_Option'$1_aggregator_Aggregator'($aggregator#$1_optional_aggregator_OptionalAggregator($t11))) <= 1)) && (LenVec($vec#$1_option_Option'$1_optional_aggregator_Integer'($integer#$1_optional_aggregator_OptionalAggregator($t11))) <= 1)));

    // assume Eq<optional_aggregator::OptionalAggregator>($t11, option::spec_borrow<optional_aggregator::OptionalAggregator>($t9)) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.move:274:26+28
    assume $IsEqual'$1_optional_aggregator_OptionalAggregator'($t11, $1_option_spec_borrow'$1_optional_aggregator_OptionalAggregator'($t9));

    // $t11 := opaque end: option::borrow<optional_aggregator::OptionalAggregator>($t9) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.move:274:26+28

    // $t13 := optional_aggregator::read($t11) on_abort goto L4 with $t8 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.move:275:25+33
    assume {:print "$at(92,10317,10350)"} true;
    call $t13 := $1_optional_aggregator_read($t11);
    if ($abort_flag) {
        assume {:print "$at(92,10317,10350)"} true;
        $t8 := $abort_code;
        assume {:print "$track_abort(23,29):", $t8} $t8 == $t8;
        goto L4;
    }

    // $t0 := opaque begin: option::some<u128>($t13) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.move:276:13+19
    assume {:print "$at(92,10364,10383)"} true;

    // assume And(WellFormed($t0), Le(Len<u128>(select option::Option.vec($t0)), 1)) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.move:276:13+19
    assume ($IsValid'$1_option_Option'u128''($t0) && (LenVec($vec#$1_option_Option'u128'($t0)) <= 1));

    // assume Eq<option::Option<u128>>($t0, option::spec_some<u128>($t13)) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.move:276:13+19
    assume $IsEqual'$1_option_Option'u128''($t0, $1_option_spec_some'u128'($t13));

    // $t0 := opaque end: option::some<u128>($t13) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.move:276:13+19

    // goto L2 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.move:272:9+315
    assume {:print "$at(92,10122,10437)"} true;
    goto L2;

    // label L0 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.move:272:9+315
L0:

    // $t0 := opaque begin: option::none<u128>() at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.move:278:13+14
    assume {:print "$at(92,10413,10427)"} true;

    // assume And(WellFormed($t0), Le(Len<u128>(select option::Option.vec($t0)), 1)) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.move:278:13+14
    assume ($IsValid'$1_option_Option'u128''($t0) && (LenVec($vec#$1_option_Option'u128'($t0)) <= 1));

    // assume Eq<option::Option<u128>>($t0, option::spec_none<u128>()) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.move:278:13+14
    assume $IsEqual'$1_option_Option'u128''($t0, $1_option_spec_none'u128'());

    // $t0 := opaque end: option::none<u128>() at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.move:278:13+14

    // label L2 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.move:272:9+315
    assume {:print "$at(92,10122,10437)"} true;
L2:

    // trace_return[0]($t0) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.move:272:9+315
    assume {:print "$at(92,10122,10437)"} true;
    assume {:print "$track_return(23,29,0):", $t0} $t0 == $t0;

    // label L3 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.move:280:5+1
    assume {:print "$at(92,10442,10443)"} true;
L3:

    // return $t0 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.move:280:5+1
    assume {:print "$at(92,10442,10443)"} true;
    $ret0 := $t0;
    return;

    // label L4 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.move:280:5+1
L4:

    // abort($t8) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.move:280:5+1
    assume {:print "$at(92,10442,10443)"} true;
    $abort_code := $t8;
    $abort_flag := true;
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

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/timestamp.spec.move:22:10+111
function {:inline} $1_timestamp_spec_now_microseconds($1_timestamp_CurrentTimeMicroseconds_$memory: $Memory $1_timestamp_CurrentTimeMicroseconds): int {
    $microseconds#$1_timestamp_CurrentTimeMicroseconds($ResourceValue($1_timestamp_CurrentTimeMicroseconds_$memory, 1))
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

// fun voting::create_proposal_v2<governance_proposal::GovernanceProposal> [baseline] at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:242:5+3273
procedure {:inline 1} $1_voting_create_proposal_v2'$1_governance_proposal_GovernanceProposal'(_$t0: int, _$t1: int, _$t2: $1_governance_proposal_GovernanceProposal, _$t3: Vec (int), _$t4: int, _$t5: int, _$t6: $1_option_Option'u128', _$t7: Table int (Vec (int)), _$t8: bool) returns ($ret0: int)
{
    // declare local variables
    var $t9: bool;
    var $t10: Table int (Vec (int));
    var $t11: int;
    var $t12: int;
    var $t13: $1_option_Option'u128';
    var $t14: int;
    var $t15: $Mutation (Table int ($1_voting_Proposal'$1_governance_proposal_GovernanceProposal'));
    var $t16: $1_string_String;
    var $t17: $Mutation (Table int (Vec (int)));
    var $t18: $1_string_String;
    var $t19: int;
    var $t20: int;
    var $t21: $1_option_Option'$1_governance_proposal_GovernanceProposal';
    var $t22: Vec (int);
    var $t23: $1_string_String;
    var $t24: int;
    var $t25: $Mutation ($1_voting_VotingForum'$1_governance_proposal_GovernanceProposal');
    var $t26: $1_voting_VotingForum'$1_governance_proposal_GovernanceProposal';
    var $t27: int;
    var $t28: $1_string_String;
    var $t29: $1_string_String;
    var $t30: bool;
    var $t31: int;
    var $t32: bool;
    var $t33: int;
    var $t34: bool;
    var $t35: int;
    var $t36: int;
    var $t37: int;
    var $t38: int;
    var $t39: bool;
    var $t40: int;
    var $t41: int;
    var $t42: $Mutation ($1_voting_VotingForum'$1_governance_proposal_GovernanceProposal');
    var $t43: int;
    var $t44: int;
    var $t45: int;
    var $t46: int;
    var $t47: $Mutation (int);
    var $t48: $Mutation (Table int (Vec (int)));
    var $t49: Vec (int);
    var $t50: $1_string_String;
    var $t51: Vec (int);
    var $t52: Vec (int);
    var $t53: $1_string_String;
    var $t54: $Mutation (Table int (Vec (int)));
    var $t55: bool;
    var $t56: Vec (int);
    var $t57: $Mutation (Table int (Vec (int)));
    var $t58: Table int (Vec (int));
    var $t59: bool;
    var $t60: $Mutation (Table int (Vec (int)));
    var $t61: $1_string_String;
    var $t62: Vec (int);
    var $t63: $Mutation (Table int ($1_voting_Proposal'$1_governance_proposal_GovernanceProposal'));
    var $t64: int;
    var $t65: $1_option_Option'$1_governance_proposal_GovernanceProposal';
    var $t66: Table int (Vec (int));
    var $t67: int;
    var $t68: int;
    var $t69: bool;
    var $t70: int;
    var $t71: $1_voting_Proposal'$1_governance_proposal_GovernanceProposal';
    var $t72: $Mutation ($1_voting_VotingEvents);
    var $t73: $Mutation ($1_event_EventHandle'$1_voting_CreateProposalEvent');
    var $t74: Table int (Vec (int));
    var $t75: $1_voting_CreateProposalEvent;
    var $t0: int;
    var $t1: int;
    var $t2: $1_governance_proposal_GovernanceProposal;
    var $t3: Vec (int);
    var $t4: int;
    var $t5: int;
    var $t6: $1_option_Option'u128';
    var $t7: Table int (Vec (int));
    var $t8: bool;
    var $temp_0'$1_governance_proposal_GovernanceProposal': $1_governance_proposal_GovernanceProposal;
    var $temp_0'$1_option_Option'u128'': $1_option_Option'u128';
    var $temp_0'$1_simple_map_SimpleMap'$1_string_String_vec'u8''': Table int (Vec (int));
    var $temp_0'$1_string_String': $1_string_String;
    var $temp_0'$1_voting_VotingForum'$1_governance_proposal_GovernanceProposal'': $1_voting_VotingForum'$1_governance_proposal_GovernanceProposal';
    var $temp_0'address': int;
    var $temp_0'bool': bool;
    var $temp_0'u128': int;
    var $temp_0'u64': int;
    var $temp_0'vec'u8'': Vec (int);
    $t0 := _$t0;
    $t1 := _$t1;
    $t2 := _$t2;
    $t3 := _$t3;
    $t4 := _$t4;
    $t5 := _$t5;
    $t6 := _$t6;
    $t7 := _$t7;
    $t8 := _$t8;

    // bytecode translation starts here
    // assume Identical($t26, global<voting::VotingForum<#0>>($t1)) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.spec.move:69:9+75
    assume {:print "$at(154,2710,2785)"} true;
    assume ($t26 == $ResourceValue($1_voting_VotingForum'$1_governance_proposal_GovernanceProposal'_$memory, $t1));

    // assume Identical($t27, select voting::VotingForum.next_proposal_id($t26)) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.spec.move:70:9+48
    assume {:print "$at(154,2794,2842)"} true;
    assume ($t27 == $next_proposal_id#$1_voting_VotingForum'$1_governance_proposal_GovernanceProposal'($t26));

    // assume Identical($t28, string::spec_utf8([73, 83, 95, 77, 85, 76, 84, 73, 95, 83, 84, 69, 80, 95, 80, 82, 79, 80, 79, 83, 65, 76, 95, 75, 69, 89])) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.spec.move:78:9+71
    assume {:print "$at(154,3361,3432)"} true;
    assume ($t28 == $1_string_spec_utf8(ConcatVec(ConcatVec(ConcatVec(ConcatVec(ConcatVec(ConcatVec(MakeVec4(73, 83, 95, 77), MakeVec4(85, 76, 84, 73)), MakeVec4(95, 83, 84, 69)), MakeVec4(80, 95, 80, 82)), MakeVec4(79, 80, 79, 83)), MakeVec4(65, 76, 95, 75)), MakeVec2(69, 89))));

    // assume Identical($t29, string::spec_utf8([73, 83, 95, 77, 85, 76, 84, 73, 95, 83, 84, 69, 80, 95, 80, 82, 79, 80, 79, 83, 65, 76, 95, 73, 78, 95, 69, 88, 69, 67, 85, 84, 73, 79, 78])) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.spec.move:81:9+101
    assume {:print "$at(154,3577,3678)"} true;
    assume ($t29 == $1_string_spec_utf8(ConcatVec(ConcatVec(ConcatVec(ConcatVec(ConcatVec(ConcatVec(ConcatVec(ConcatVec(MakeVec4(73, 83, 95, 77), MakeVec4(85, 76, 84, 73)), MakeVec4(95, 83, 84, 69)), MakeVec4(80, 95, 80, 82)), MakeVec4(79, 80, 79, 83)), MakeVec4(65, 76, 95, 73)), MakeVec4(78, 95, 69, 88)), MakeVec4(69, 67, 85, 84)), MakeVec3(73, 79, 78))));

    // assume chain_status::$is_operating() at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.spec.move:57:9+38
    assume {:print "$at(154,2295,2333)"} true;
    assume $1_chain_status_$is_operating($1_chain_status_GenesisEndMarker_$memory);

    // trace_local[proposer]($t0) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:242:5+1
    assume {:print "$at(153,12699,12700)"} true;
    assume {:print "$track_local(30,2,0):", $t0} $t0 == $t0;

    // trace_local[voting_forum_address]($t1) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:242:5+1
    assume {:print "$track_local(30,2,1):", $t1} $t1 == $t1;

    // trace_local[execution_content]($t2) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:242:5+1
    assume {:print "$track_local(30,2,2):", $t2} $t2 == $t2;

    // trace_local[execution_hash]($t3) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:242:5+1
    assume {:print "$track_local(30,2,3):", $t3} $t3 == $t3;

    // trace_local[min_vote_threshold]($t4) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:242:5+1
    assume {:print "$track_local(30,2,4):", $t4} $t4 == $t4;

    // trace_local[expiration_secs]($t5) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:242:5+1
    assume {:print "$track_local(30,2,5):", $t5} $t5 == $t5;

    // trace_local[early_resolution_vote_threshold]($t6) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:242:5+1
    assume {:print "$track_local(30,2,6):", $t6} $t6 == $t6;

    // trace_local[metadata]($t7) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:242:5+1
    assume {:print "$track_local(30,2,7):", $t7} $t7 == $t7;

    // trace_local[is_multi_step_proposal]($t8) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:242:5+1
    assume {:print "$track_local(30,2,8):", $t8} $t8 == $t8;

    // $t30 := opaque begin: option::is_some<u128>($t6) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:253:13+49
    assume {:print "$at(153,13146,13195)"} true;

    // assume WellFormed($t30) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:253:13+49
    assume $IsValid'bool'($t30);

    // assume Eq<bool>($t30, option::spec_is_some<u128>($t6)) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:253:13+49
    assume $IsEqual'bool'($t30, $1_option_spec_is_some'u128'($t6));

    // $t30 := opaque end: option::is_some<u128>($t6) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:253:13+49

    // if ($t30) goto L1 else goto L0 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:253:9+261
    if ($t30) { goto L1; } else { goto L0; }

    // label L1 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:255:17+18
    assume {:print "$at(153,13236,13254)"} true;
L1:

    // $t31 := opaque begin: option::borrow<u128>($t6) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:255:40+48
    assume {:print "$at(153,13259,13307)"} true;

    // assume Identical($t32, option::spec_is_none<u128>($t6)) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:255:40+48
    assume ($t32 == $1_option_spec_is_none'u128'($t6));

    // if ($t32) goto L14 else goto L13 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:255:40+48
    if ($t32) { goto L14; } else { goto L13; }

    // label L14 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:255:40+48
L14:

    // assume And(option::spec_is_none<u128>($t6), Eq(262145, $t33)) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:255:40+48
    assume {:print "$at(153,13259,13307)"} true;
    assume ($1_option_spec_is_none'u128'($t6) && $IsEqual'num'(262145, $t33));

    // trace_abort($t33) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:255:40+48
    assume {:print "$at(153,13259,13307)"} true;
    assume {:print "$track_abort(30,2):", $t33} $t33 == $t33;

    // goto L12 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:255:40+48
    goto L12;

    // label L13 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:255:40+48
L13:

    // assume WellFormed($t31) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:255:40+48
    assume {:print "$at(153,13259,13307)"} true;
    assume $IsValid'u128'($t31);

    // assume Eq<u128>($t31, option::spec_borrow<u128>($t6)) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:255:40+48
    assume $IsEqual'u128'($t31, $1_option_spec_borrow'u128'($t6));

    // $t31 := opaque end: option::borrow<u128>($t6) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:255:40+48

    // $t34 := <=($t4, $t31) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:255:36+2
    call $t34 := $Le($t4, $t31);

    // if ($t34) goto L3 else goto L2 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:254:13+181
    assume {:print "$at(153,13211,13392)"} true;
    if ($t34) { goto L3; } else { goto L2; }

    // label L3 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:254:13+181
L3:

    // goto L0 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:254:13+181
    assume {:print "$at(153,13211,13392)"} true;
    goto L0;

    // label L2 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:256:41+27
    assume {:print "$at(153,13349,13376)"} true;
L2:

    // $t35 := 7 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:256:41+27
    assume {:print "$at(153,13349,13376)"} true;
    $t35 := 7;
    assume $IsValid'u64'($t35);

    // $t36 := error::invalid_argument($t35) on_abort goto L12 with $t33 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:256:17+52
    call $t36 := $1_error_invalid_argument($t35);
    if ($abort_flag) {
        assume {:print "$at(153,13325,13377)"} true;
        $t33 := $abort_code;
        assume {:print "$track_abort(30,2):", $t33} $t33 == $t33;
        goto L12;
    }

    // trace_abort($t36) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:254:13+181
    assume {:print "$at(153,13211,13392)"} true;
    assume {:print "$track_abort(30,2):", $t36} $t36 == $t36;

    // $t33 := move($t36) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:254:13+181
    $t33 := $t36;

    // goto L12 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:254:13+181
    goto L12;

    // label L0 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:260:32+15
    assume {:print "$at(153,13499,13514)"} true;
L0:

    // $t37 := vector::length<u8>($t3) on_abort goto L12 with $t33 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:260:17+31
    assume {:print "$at(153,13484,13515)"} true;
    call $t37 := $1_vector_length'u8'($t3);
    if ($abort_flag) {
        assume {:print "$at(153,13484,13515)"} true;
        $t33 := $abort_code;
        assume {:print "$track_abort(30,2):", $t33} $t33 == $t33;
        goto L12;
    }

    // $t38 := 0 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:260:51+1
    $t38 := 0;
    assume $IsValid'u64'($t38);

    // $t39 := >($t37, $t38) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:260:49+1
    call $t39 := $Gt($t37, $t38);

    // if ($t39) goto L5 else goto L4 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:260:9+101
    if ($t39) { goto L5; } else { goto L4; }

    // label L5 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:260:9+101
L5:

    // goto L6 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:260:9+101
    assume {:print "$at(153,13476,13577)"} true;
    goto L6;

    // label L4 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:260:78+30
L4:

    // $t40 := 4 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:260:78+30
    assume {:print "$at(153,13545,13575)"} true;
    $t40 := 4;
    assume $IsValid'u64'($t40);

    // $t41 := error::invalid_argument($t40) on_abort goto L12 with $t33 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:260:54+55
    call $t41 := $1_error_invalid_argument($t40);
    if ($abort_flag) {
        assume {:print "$at(153,13521,13576)"} true;
        $t33 := $abort_code;
        assume {:print "$track_abort(30,2):", $t33} $t33 == $t33;
        goto L12;
    }

    // trace_abort($t41) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:260:9+101
    assume {:print "$at(153,13476,13577)"} true;
    assume {:print "$track_abort(30,2):", $t41} $t41 == $t41;

    // $t33 := move($t41) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:260:9+101
    $t33 := $t41;

    // goto L12 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:260:9+101
    goto L12;

    // label L6 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:262:73+20
    assume {:print "$at(153,13652,13672)"} true;
L6:

    // $t42 := borrow_global<voting::VotingForum<#0>>($t1) on_abort goto L12 with $t33 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:262:28+17
    assume {:print "$at(153,13607,13624)"} true;
    if (!$ResourceExists($1_voting_VotingForum'$1_governance_proposal_GovernanceProposal'_$memory, $t1)) {
        call $ExecFailureAbort();
    } else {
        $t42 := $Mutation($Global($t1), EmptyVec(), $ResourceValue($1_voting_VotingForum'$1_governance_proposal_GovernanceProposal'_$memory, $t1));
    }
    if ($abort_flag) {
        assume {:print "$at(153,13607,13624)"} true;
        $t33 := $abort_code;
        assume {:print "$track_abort(30,2):", $t33} $t33 == $t33;
        goto L12;
    }

    // trace_local[voting_forum]($t42) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:262:13+12
    $temp_0'$1_voting_VotingForum'$1_governance_proposal_GovernanceProposal'' := $Dereference($t42);
    assume {:print "$track_local(30,2,25):", $temp_0'$1_voting_VotingForum'$1_governance_proposal_GovernanceProposal''} $temp_0'$1_voting_VotingForum'$1_governance_proposal_GovernanceProposal'' == $temp_0'$1_voting_VotingForum'$1_governance_proposal_GovernanceProposal'';

    // $t43 := get_field<voting::VotingForum<#0>>.next_proposal_id($t42) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:263:27+29
    assume {:print "$at(153,13701,13730)"} true;
    $t43 := $next_proposal_id#$1_voting_VotingForum'$1_governance_proposal_GovernanceProposal'($Dereference($t42));

    // trace_local[proposal_id]($t43) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:263:13+11
    assume {:print "$track_local(30,2,24):", $t43} $t43 == $t43;

    // $t44 := get_field<voting::VotingForum<#0>>.next_proposal_id($t42) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:264:41+29
    assume {:print "$at(153,13772,13801)"} true;
    $t44 := $next_proposal_id#$1_voting_VotingForum'$1_governance_proposal_GovernanceProposal'($Dereference($t42));

    // $t45 := 1 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:264:73+1
    $t45 := 1;
    assume $IsValid'u64'($t45);

    // $t46 := +($t44, $t45) on_abort goto L12 with $t33 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:264:71+1
    call $t46 := $AddU64($t44, $t45);
    if ($abort_flag) {
        assume {:print "$at(153,13802,13803)"} true;
        $t33 := $abort_code;
        assume {:print "$track_abort(30,2):", $t33} $t33 == $t33;
        goto L12;
    }

    // $t47 := borrow_field<voting::VotingForum<#0>>.next_proposal_id($t42) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:264:9+29
    $t47 := $ChildMutation($t42, 2, $next_proposal_id#$1_voting_VotingForum'$1_governance_proposal_GovernanceProposal'($Dereference($t42)));

    // write_ref($t47, $t46) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:264:9+65
    $t47 := $UpdateMutation($t47, $t46);

    // write_back[Reference($t42).next_proposal_id (u64)]($t47) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:264:9+65
    $t42 := $UpdateMutation($t42, $Update'$1_voting_VotingForum'$1_governance_proposal_GovernanceProposal''_next_proposal_id($Dereference($t42), $Dereference($t47)));

    // $t48 := borrow_local($t7) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:267:25+13
    assume {:print "$at(153,13913,13926)"} true;
    $t48 := $Mutation($Local(7), EmptyVec(), $t7);

    // $t49 := [73, 83, 95, 77, 85, 76, 84, 73, 95, 83, 84, 69, 80, 95, 80, 82, 79, 80, 79, 83, 65, 76, 95, 75, 69, 89] at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:267:45+26
    $t49 := ConcatVec(ConcatVec(ConcatVec(ConcatVec(ConcatVec(ConcatVec(MakeVec4(73, 83, 95, 77), MakeVec4(85, 76, 84, 73)), MakeVec4(95, 83, 84, 69)), MakeVec4(80, 95, 80, 82)), MakeVec4(79, 80, 79, 83)), MakeVec4(65, 76, 95, 75)), MakeVec2(69, 89));
    assume $IsValid'vec'u8''($t49);

    // $t50 := string::utf8($t49) on_abort goto L12 with $t33 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:267:40+32
    call $t50 := $1_string_utf8($t49);
    if ($abort_flag) {
        assume {:print "$at(153,13928,13960)"} true;
        $t33 := $abort_code;
        assume {:print "$track_abort(30,2):", $t33} $t33 == $t33;
        goto L12;
    }

    // $t51 := bcs::to_bytes<bool>($t8) on_abort goto L12 with $t33 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:267:74+33
    call $t51 := $1_bcs_to_bytes'bool'($t8);
    if ($abort_flag) {
        assume {:print "$at(153,13962,13995)"} true;
        $t33 := $abort_code;
        assume {:print "$track_abort(30,2):", $t33} $t33 == $t33;
        goto L12;
    }

    // simple_map::add<string::String, vector<u8>>($t48, $t50, $t51) on_abort goto L12 with $t33 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:267:9+99
    call $t48 := $1_simple_map_add'$1_string_String_vec'u8''($t48, $t50, $t51);
    if ($abort_flag) {
        assume {:print "$at(153,13897,13996)"} true;
        $t33 := $abort_code;
        assume {:print "$track_abort(30,2):", $t33} $t33 == $t33;
        goto L12;
    }

    // write_back[LocalRoot($t7)@]($t48) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:267:9+99
    $t7 := $Dereference($t48);

    // trace_local[metadata]($t7) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:267:9+99
    assume {:print "$track_local(30,2,7):", $t7} $t7 == $t7;

    // $t52 := [73, 83, 95, 77, 85, 76, 84, 73, 95, 83, 84, 69, 80, 95, 80, 82, 79, 80, 79, 83, 65, 76, 95, 73, 78, 95, 69, 88, 69, 67, 85, 84, 73, 79, 78] at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:269:51+39
    assume {:print "$at(153,14049,14088)"} true;
    $t52 := ConcatVec(ConcatVec(ConcatVec(ConcatVec(ConcatVec(ConcatVec(ConcatVec(ConcatVec(MakeVec4(73, 83, 95, 77), MakeVec4(85, 76, 84, 73)), MakeVec4(95, 83, 84, 69)), MakeVec4(80, 95, 80, 82)), MakeVec4(79, 80, 79, 83)), MakeVec4(65, 76, 95, 73)), MakeVec4(78, 95, 69, 88)), MakeVec4(69, 67, 85, 84)), MakeVec3(73, 79, 78));
    assume $IsValid'vec'u8''($t52);

    // $t53 := string::utf8($t52) on_abort goto L12 with $t33 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:269:46+45
    call $t53 := $1_string_utf8($t52);
    if ($abort_flag) {
        assume {:print "$at(153,14044,14089)"} true;
        $t33 := $abort_code;
        assume {:print "$track_abort(30,2):", $t33} $t33 == $t33;
        goto L12;
    }

    // trace_local[is_multi_step_in_execution_key]($t53) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:269:13+30
    assume {:print "$track_local(30,2,23):", $t53} $t53 == $t53;

    // if ($t8) goto L8 else goto L7 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:270:9+951
    assume {:print "$at(153,14099,15050)"} true;
    if ($t8) { goto L8; } else { goto L7; }

    // label L8 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:274:29+13
    assume {:print "$at(153,14536,14549)"} true;
L8:

    // $t54 := borrow_local($t7) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:274:29+13
    assume {:print "$at(153,14536,14549)"} true;
    $t54 := $Mutation($Local(7), EmptyVec(), $t7);

    // $t55 := false at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:274:86+5
    $t55 := false;
    assume $IsValid'bool'($t55);

    // $t56 := bcs::to_bytes<bool>($t55) on_abort goto L12 with $t33 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:274:76+16
    call $t56 := $1_bcs_to_bytes'bool'($t55);
    if ($abort_flag) {
        assume {:print "$at(153,14583,14599)"} true;
        $t33 := $abort_code;
        assume {:print "$track_abort(30,2):", $t33} $t33 == $t33;
        goto L12;
    }

    // simple_map::add<string::String, vector<u8>>($t54, $t53, $t56) on_abort goto L12 with $t33 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:274:13+80
    call $t54 := $1_simple_map_add'$1_string_String_vec'u8''($t54, $t53, $t56);
    if ($abort_flag) {
        assume {:print "$at(153,14520,14600)"} true;
        $t33 := $abort_code;
        assume {:print "$track_abort(30,2):", $t33} $t33 == $t33;
        goto L12;
    }

    // write_back[LocalRoot($t7)@]($t54) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:274:13+80
    $t7 := $Dereference($t54);

    // trace_local[metadata]($t7) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:274:13+80
    assume {:print "$track_local(30,2,7):", $t7} $t7 == $t7;

    // goto L9 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:274:93+1
    goto L9;

    // label L7 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:277:45+13
    assume {:print "$at(153,14910,14923)"} true;
L7:

    // $t57 := borrow_local($t7) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:277:45+13
    assume {:print "$at(153,14910,14923)"} true;
    $t57 := $Mutation($Local(7), EmptyVec(), $t7);

    // $t58 := read_ref($t57) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:277:44+48
    $t58 := $Dereference($t57);

    // trace_local[metadata]($t7) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:277:44+48
    assume {:print "$track_local(30,2,7):", $t7} $t7 == $t7;

    // $t59 := simple_map::contains_key<string::String, vector<u8>>($t58, $t53) on_abort goto L12 with $t33 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:277:20+72
    call $t59 := $1_simple_map_contains_key'$1_string_String_vec'u8''($t58, $t53);
    if ($abort_flag) {
        assume {:print "$at(153,14885,14957)"} true;
        $t33 := $abort_code;
        assume {:print "$track_abort(30,2):", $t33} $t33 == $t33;
        goto L12;
    }

    // if ($t59) goto L10 else goto L9 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:277:16+169
    if ($t59) { goto L10; } else { goto L9; }

    // label L10 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:278:32+13
    assume {:print "$at(153,14992,15005)"} true;
L10:

    // $t60 := borrow_local($t7) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:278:32+13
    assume {:print "$at(153,14992,15005)"} true;
    $t60 := $Mutation($Local(7), EmptyVec(), $t7);

    // ($t61, $t62) := simple_map::remove<string::String, vector<u8>>($t60, $t53) on_abort goto L12 with $t33 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:278:13+66
    call $t61,$t62,$t60 := $1_simple_map_remove'$1_string_String_vec'u8''($t60, $t53);
    if ($abort_flag) {
        assume {:print "$at(153,14973,15039)"} true;
        $t33 := $abort_code;
        assume {:print "$track_abort(30,2):", $t33} $t33 == $t33;
        goto L12;
    }

    // write_back[LocalRoot($t7)@]($t60) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:278:13+66
    $t7 := $Dereference($t60);

    // trace_local[metadata]($t7) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:278:13+66
    assume {:print "$track_local(30,2,7):", $t7} $t7 == $t7;

    // destroy($t62) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:278:13+66

    // destroy($t61) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:278:13+66

    // label L9 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:281:25+12
    assume {:print "$at(153,15077,15089)"} true;
L9:

    // $t63 := borrow_field<voting::VotingForum<#0>>.proposals($t42) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:281:20+27
    assume {:print "$at(153,15072,15099)"} true;
    $t63 := $ChildMutation($t42, 0, $proposals#$1_voting_VotingForum'$1_governance_proposal_GovernanceProposal'($Dereference($t42)));

    // $t64 := timestamp::now_seconds() on_abort goto L12 with $t33 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:283:33+24
    assume {:print "$at(153,15179,15203)"} true;
    call $t64 := $1_timestamp_now_seconds();
    if ($abort_flag) {
        assume {:print "$at(153,15179,15203)"} true;
        $t33 := $abort_code;
        assume {:print "$track_abort(30,2):", $t33} $t33 == $t33;
        goto L12;
    }

    // $t65 := opaque begin: option::some<#0>($t2) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:284:32+45
    assume {:print "$at(153,15236,15281)"} true;

    // assume And(WellFormed($t65), Le(Len<#0>(select option::Option.vec($t65)), 1)) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:284:32+45
    assume ($IsValid'$1_option_Option'$1_governance_proposal_GovernanceProposal''($t65) && (LenVec($vec#$1_option_Option'$1_governance_proposal_GovernanceProposal'($t65)) <= 1));

    // assume Eq<option::Option<#0>>($t65, option::spec_some<#0>($t2)) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:284:32+45
    assume $IsEqual'$1_option_Option'$1_governance_proposal_GovernanceProposal''($t65, $1_option_spec_some'$1_governance_proposal_GovernanceProposal'($t2));

    // $t65 := opaque end: option::some<#0>($t2) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:284:32+45

    // $t66 := copy($t7) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:286:13+8
    assume {:print "$at(153,15323,15331)"} true;
    $t66 := $t7;

    // $t67 := 0 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:290:24+1
    assume {:print "$at(153,15462,15463)"} true;
    $t67 := 0;
    assume $IsValid'u128'($t67);

    // $t68 := 0 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:291:23+1
    assume {:print "$at(153,15487,15488)"} true;
    $t68 := 0;
    assume $IsValid'u128'($t68);

    // $t69 := false at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:292:26+5
    assume {:print "$at(153,15515,15520)"} true;
    $t69 := false;
    assume $IsValid'bool'($t69);

    // $t70 := 0 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:293:35+1
    assume {:print "$at(153,15556,15557)"} true;
    $t70 := 0;
    assume $IsValid'u64'($t70);

    // $t71 := pack voting::Proposal<#0>($t0, $t65, $t66, $t64, $t3, $t4, $t5, $t6, $t67, $t68, $t69, $t70) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:281:62+454
    assume {:print "$at(153,15114,15568)"} true;
    $t71 := $1_voting_Proposal'$1_governance_proposal_GovernanceProposal'($t0, $t65, $t66, $t64, $t3, $t4, $t5, $t6, $t67, $t68, $t69, $t70);

    // table::add<u64, voting::Proposal<#0>>($t63, $t43, $t71) on_abort goto L12 with $t33 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:281:9+508
    call $t63 := $1_table_add'u64_$1_voting_Proposal'$1_governance_proposal_GovernanceProposal''($t63, $t43, $t71);
    if ($abort_flag) {
        assume {:print "$at(153,15061,15569)"} true;
        $t33 := $abort_code;
        assume {:print "$track_abort(30,2):", $t33} $t33 == $t33;
        goto L12;
    }

    // write_back[Reference($t42).proposals (table::Table<u64, voting::Proposal<#0>>)]($t63) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:281:9+508
    $t42 := $UpdateMutation($t42, $Update'$1_voting_VotingForum'$1_governance_proposal_GovernanceProposal''_proposals($Dereference($t42), $Dereference($t63)));

    // $t72 := borrow_field<voting::VotingForum<#0>>.events($t42) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:297:18+19
    assume {:print "$at(153,15637,15656)"} true;
    $t72 := $ChildMutation($t42, 1, $events#$1_voting_VotingForum'$1_governance_proposal_GovernanceProposal'($Dereference($t42)));

    // $t73 := borrow_field<voting::VotingEvents>.create_proposal_events($t72) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:297:13+47
    $t73 := $ChildMutation($t72, 0, $create_proposal_events#$1_voting_VotingEvents($Dereference($t72)));

    // $t74 := move($t7) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:303:17+8
    assume {:print "$at(153,15874,15882)"} true;
    $t74 := $t7;

    // $t75 := pack voting::CreateProposalEvent($t43, $t6, $t3, $t5, $t74, $t4) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:298:13+240
    assume {:print "$at(153,15693,15933)"} true;
    $t75 := $1_voting_CreateProposalEvent($t43, $t6, $t3, $t5, $t74, $t4);

    // opaque begin: event::emit_event<voting::CreateProposalEvent>($t73, $t75) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:296:9+364
    assume {:print "$at(153,15580,15944)"} true;

    // opaque end: event::emit_event<voting::CreateProposalEvent>($t73, $t75) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:296:9+364

    // write_back[Reference($t72).create_proposal_events (event::EventHandle<voting::CreateProposalEvent>)]($t73) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:296:9+364
    $t72 := $UpdateMutation($t72, $Update'$1_voting_VotingEvents'_create_proposal_events($Dereference($t72), $Dereference($t73)));

    // write_back[Reference($t42).events (voting::VotingEvents)]($t72) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:296:9+364
    $t42 := $UpdateMutation($t42, $Update'$1_voting_VotingForum'$1_governance_proposal_GovernanceProposal''_events($Dereference($t42), $Dereference($t72)));

    // pack_ref_deep($t42) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:296:9+364

    // write_back[voting::VotingForum<#0>@]($t42) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:296:9+364
    $1_voting_VotingForum'$1_governance_proposal_GovernanceProposal'_$memory := $ResourceUpdate($1_voting_VotingForum'$1_governance_proposal_GovernanceProposal'_$memory, $GlobalLocationAddress($t42),
        $Dereference($t42));

    // trace_return[0]($t43) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:308:9+11
    assume {:print "$at(153,15955,15966)"} true;
    assume {:print "$track_return(30,2,0):", $t43} $t43 == $t43;

    // label L11 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:309:5+1
    assume {:print "$at(153,15971,15972)"} true;
L11:

    // return $t43 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:309:5+1
    assume {:print "$at(153,15971,15972)"} true;
    $ret0 := $t43;
    return;

    // label L12 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:309:5+1
L12:

    // abort($t33) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.move:309:5+1
    assume {:print "$at(153,15971,15972)"} true;
    $abort_code := $t33;
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

// fun staking_config::get [baseline] at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/configs/staking_config.move:169:5+118
procedure {:inline 1} $1_staking_config_get() returns ($ret0: $1_staking_config_StakingConfig)
{
    // declare local variables
    var $t0: int;
    var $t1: $1_staking_config_StakingConfig;
    var $t2: int;
    var $temp_0'$1_staking_config_StakingConfig': $1_staking_config_StakingConfig;

    // bytecode translation starts here
    // $t0 := 0x1 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/configs/staking_config.move:170:39+16
    assume {:print "$at(100,8264,8280)"} true;
    $t0 := 1;
    assume $IsValid'address'($t0);

    // $t1 := get_global<staking_config::StakingConfig>($t0) on_abort goto L2 with $t2 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/configs/staking_config.move:170:10+13
    if (!$ResourceExists($1_staking_config_StakingConfig_$memory, $t0)) {
        call $ExecFailureAbort();
    } else {
        $t1 := $ResourceValue($1_staking_config_StakingConfig_$memory, $t0);
    }
    if ($abort_flag) {
        assume {:print "$at(100,8235,8248)"} true;
        $t2 := $abort_code;
        assume {:print "$track_abort(35,2):", $t2} $t2 == $t2;
        goto L2;
    }

    // trace_return[0]($t1) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/configs/staking_config.move:170:9+47
    assume {:print "$track_return(35,2,0):", $t1} $t1 == $t1;

    // label L1 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/configs/staking_config.move:171:5+1
    assume {:print "$at(100,8286,8287)"} true;
L1:

    // return $t1 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/configs/staking_config.move:171:5+1
    assume {:print "$at(100,8286,8287)"} true;
    $ret0 := $t1;
    return;

    // label L2 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/configs/staking_config.move:171:5+1
L2:

    // abort($t2) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/configs/staking_config.move:171:5+1
    assume {:print "$at(100,8286,8287)"} true;
    $abort_code := $t2;
    $abort_flag := true;
    return;

}

// fun staking_config::get_allow_validator_set_change [baseline] at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/configs/staking_config.move:174:5+121
procedure {:inline 1} $1_staking_config_get_allow_validator_set_change(_$t0: $1_staking_config_StakingConfig) returns ($ret0: bool)
{
    // declare local variables
    var $t1: bool;
    var $t0: $1_staking_config_StakingConfig;
    var $temp_0'$1_staking_config_StakingConfig': $1_staking_config_StakingConfig;
    var $temp_0'bool': bool;
    $t0 := _$t0;

    // bytecode translation starts here
    // trace_local[config]($t0) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/configs/staking_config.move:174:5+1
    assume {:print "$at(100,8350,8351)"} true;
    assume {:print "$track_local(35,3,0):", $t0} $t0 == $t0;

    // $t1 := get_field<staking_config::StakingConfig>.allow_validator_set_change($t0) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/configs/staking_config.move:175:9+33
    assume {:print "$at(100,8432,8465)"} true;
    $t1 := $allow_validator_set_change#$1_staking_config_StakingConfig($t0);

    // trace_return[0]($t1) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/configs/staking_config.move:175:9+33
    assume {:print "$track_return(35,3,0):", $t1} $t1 == $t1;

    // label L1 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/configs/staking_config.move:176:5+1
    assume {:print "$at(100,8470,8471)"} true;
L1:

    // return $t1 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/configs/staking_config.move:176:5+1
    assume {:print "$at(100,8470,8471)"} true;
    $ret0 := $t1;
    return;

}

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/stake.spec.move:16:10+500
function {:inline} $1_stake_validator_set_is_valid($1_stake_StakePool_$memory: $Memory $1_stake_StakePool, $1_stake_ValidatorConfig_$memory: $Memory $1_stake_ValidatorConfig, $1_stake_ValidatorPerformance_$memory: $Memory $1_stake_ValidatorPerformance, $1_stake_ValidatorSet_$memory: $Memory $1_stake_ValidatorSet): bool {
    (var validator_set := $ResourceValue($1_stake_ValidatorSet_$memory, 1); (((($1_stake_spec_validators_are_initialized($1_stake_StakePool_$memory, $1_stake_ValidatorConfig_$memory, $active_validators#$1_stake_ValidatorSet(validator_set)) && $1_stake_spec_validators_are_initialized($1_stake_StakePool_$memory, $1_stake_ValidatorConfig_$memory, $pending_inactive#$1_stake_ValidatorSet(validator_set))) && $1_stake_spec_validators_are_initialized($1_stake_StakePool_$memory, $1_stake_ValidatorConfig_$memory, $pending_active#$1_stake_ValidatorSet(validator_set))) && $1_stake_spec_validator_indices_are_valid($1_stake_ValidatorConfig_$memory, $1_stake_ValidatorPerformance_$memory, $active_validators#$1_stake_ValidatorSet(validator_set))) && $1_stake_spec_validator_indices_are_valid($1_stake_ValidatorConfig_$memory, $1_stake_ValidatorPerformance_$memory, $pending_inactive#$1_stake_ValidatorSet(validator_set))))
}

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/stake.spec.move:299:10+241
function {:inline} $1_stake_spec_validators_are_initialized($1_stake_StakePool_$memory: $Memory $1_stake_StakePool, $1_stake_ValidatorConfig_$memory: $Memory $1_stake_ValidatorConfig, validators: Vec ($1_stake_ValidatorInfo)): bool {
    (var $range_0 := $Range(0, LenVec(validators)); (forall $i_1: int :: $InRange($range_0, $i_1) ==> (var i := $i_1;
    (($1_stake_spec_has_stake_pool($1_stake_StakePool_$memory, $addr#$1_stake_ValidatorInfo(ReadVec(validators, i))) && $1_stake_spec_has_validator_config($1_stake_ValidatorConfig_$memory, $addr#$1_stake_ValidatorInfo(ReadVec(validators, i))))))))
}

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/stake.spec.move:306:10+234
function {:inline} $1_stake_spec_validator_indices_are_valid($1_stake_ValidatorConfig_$memory: $Memory $1_stake_ValidatorConfig, $1_stake_ValidatorPerformance_$memory: $Memory $1_stake_ValidatorPerformance, validators: Vec ($1_stake_ValidatorInfo)): bool {
    (var $range_2 := $Range(0, LenVec(validators)); (forall $i_3: int :: $InRange($range_2, $i_3) ==> (var i := $i_3;
    (($validator_index#$1_stake_ValidatorConfig($ResourceValue($1_stake_ValidatorConfig_$memory, $addr#$1_stake_ValidatorInfo(ReadVec(validators, i)))) < $1_stake_spec_validator_index_upper_bound($1_stake_ValidatorPerformance_$memory))))))
}

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/stake.spec.move:312:10+122
function {:inline} $1_stake_spec_validator_index_upper_bound($1_stake_ValidatorPerformance_$memory: $Memory $1_stake_ValidatorPerformance): int {
    LenVec($validators#$1_stake_ValidatorPerformance($ResourceValue($1_stake_ValidatorPerformance_$memory, 1)))
}

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/stake.spec.move:316:10+78
function {:inline} $1_stake_spec_has_stake_pool($1_stake_StakePool_$memory: $Memory $1_stake_StakePool, a: int): bool {
    $ResourceExists($1_stake_StakePool_$memory, a)
}

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/stake.spec.move:320:10+90
function {:inline} $1_stake_spec_has_validator_config($1_stake_ValidatorConfig_$memory: $Memory $1_stake_ValidatorConfig, a: int): bool {
    $ResourceExists($1_stake_ValidatorConfig_$memory, a)
}

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/stake.spec.move:333:10+148
function {:inline} $1_stake_spec_contains(validators: Vec ($1_stake_ValidatorInfo), addr: int): bool {
    (var $range_4 := $Range(0, LenVec(validators)); (exists $i_5: int :: $InRange($range_4, $i_5) && (var i := $i_5;
    ($IsEqual'address'($addr#$1_stake_ValidatorInfo(ReadVec(validators, i)), addr)))))
}

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/stake.spec.move:337:10+360
function {:inline} $1_stake_spec_is_current_epoch_validator($1_stake_ValidatorSet_$memory: $Memory $1_stake_ValidatorSet, pool_address: int): bool {
    (var validator_set := $ResourceValue($1_stake_ValidatorSet_$memory, 1); (!$1_stake_spec_contains($pending_active#$1_stake_ValidatorSet(validator_set), pool_address) && ($1_stake_spec_contains($active_validators#$1_stake_ValidatorSet(validator_set), pool_address) || $1_stake_spec_contains($pending_inactive#$1_stake_ValidatorSet(validator_set), pool_address))))
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

// fun stake::assert_stake_pool_exists [baseline] at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/stake.move:1325:5+162
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
    // trace_local[pool_address]($t0) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/stake.move:1325:5+1
    assume {:print "$at(129,63127,63128)"} true;
    assume {:print "$track_local(38,5,0):", $t0} $t0 == $t0;

    // $t1 := stake::stake_pool_exists($t0) on_abort goto L4 with $t2 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/stake.move:1326:17+31
    assume {:print "$at(129,63197,63228)"} true;
    call $t1 := $1_stake_stake_pool_exists($t0);
    if ($abort_flag) {
        assume {:print "$at(129,63197,63228)"} true;
        $t2 := $abort_code;
        assume {:print "$track_abort(38,5):", $t2} $t2 == $t2;
        goto L4;
    }

    // if ($t1) goto L1 else goto L0 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/stake.move:1326:9+93
    if ($t1) { goto L1; } else { goto L0; }

    // label L1 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/stake.move:1326:9+93
L1:

    // goto L2 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/stake.move:1326:9+93
    assume {:print "$at(129,63189,63282)"} true;
    goto L2;

    // label L0 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/stake.move:1326:74+26
L0:

    // $t3 := 14 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/stake.move:1326:74+26
    assume {:print "$at(129,63254,63280)"} true;
    $t3 := 14;
    assume $IsValid'u64'($t3);

    // $t4 := error::invalid_argument($t3) on_abort goto L4 with $t2 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/stake.move:1326:50+51
    call $t4 := $1_error_invalid_argument($t3);
    if ($abort_flag) {
        assume {:print "$at(129,63230,63281)"} true;
        $t2 := $abort_code;
        assume {:print "$track_abort(38,5):", $t2} $t2 == $t2;
        goto L4;
    }

    // trace_abort($t4) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/stake.move:1326:9+93
    assume {:print "$at(129,63189,63282)"} true;
    assume {:print "$track_abort(38,5):", $t4} $t4 == $t4;

    // $t2 := move($t4) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/stake.move:1326:9+93
    $t2 := $t4;

    // goto L4 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/stake.move:1326:9+93
    goto L4;

    // label L2 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/stake.move:1326:102+1
L2:

    // label L3 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/stake.move:1327:5+1
    assume {:print "$at(129,63288,63289)"} true;
L3:

    // return () at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/stake.move:1327:5+1
    assume {:print "$at(129,63288,63289)"} true;
    return;

    // label L4 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/stake.move:1327:5+1
L4:

    // abort($t2) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/stake.move:1327:5+1
    assume {:print "$at(129,63288,63289)"} true;
    $abort_code := $t2;
    $abort_flag := true;
    return;

}

// fun stake::get_current_epoch_voting_power [baseline] at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/stake.move:344:5+724
procedure {:inline 1} $1_stake_get_current_epoch_voting_power(_$t0: int) returns ($ret0: int)
{
    // declare local variables
    var $t1: bool;
    var $t2: int;
    var $t3: int;
    var $t4: int;
    var $t5: int;
    var $t6: int;
    var $t7: $1_stake_ValidatorSet;
    var $t8: int;
    var $t9: int;
    var $t10: bool;
    var $t11: bool;
    var $t12: int;
    var $t13: $1_stake_StakePool;
    var $t14: $1_coin_Coin'$1_aptos_coin_AptosCoin';
    var $t15: int;
    var $t16: $1_stake_StakePool;
    var $t17: $1_coin_Coin'$1_aptos_coin_AptosCoin';
    var $t18: int;
    var $t19: int;
    var $t0: int;
    var $temp_0'address': int;
    var $temp_0'u64': int;
    $t0 := _$t0;

    // bytecode translation starts here
    // trace_local[pool_address]($t0) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/stake.move:344:5+1
    assume {:print "$at(129,15504,15505)"} true;
    assume {:print "$track_local(38,15,0):", $t0} $t0 == $t0;

    // stake::assert_stake_pool_exists($t0) on_abort goto L7 with $t6 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/stake.move:345:9+38
    assume {:print "$at(129,15617,15655)"} true;
    call $1_stake_assert_stake_pool_exists($t0);
    if ($abort_flag) {
        assume {:print "$at(129,15617,15655)"} true;
        $t6 := $abort_code;
        assume {:print "$track_abort(38,15):", $t6} $t6 == $t6;
        goto L7;
    }

    // assume Identical($t7, global<stake::ValidatorSet>(1)) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/stake.spec.move:239:9+59
    assume {:print "$at(130,10286,10345)"} true;
    assume ($t7 == $ResourceValue($1_stake_ValidatorSet_$memory, 1));

    // $t8 := stake::get_validator_state($t0) on_abort goto L7 with $t6 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/stake.move:346:31+33
    assume {:print "$at(129,15687,15720)"} true;
    call $t8 := $1_stake_get_validator_state($t0);
    if ($abort_flag) {
        assume {:print "$at(129,15687,15720)"} true;
        $t6 := $abort_code;
        assume {:print "$track_abort(38,15):", $t6} $t6 == $t6;
        goto L7;
    }

    // trace_local[validator_state]($t8) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/stake.move:346:13+15
    assume {:print "$track_local(38,15,5):", $t8} $t8 == $t8;

    // $t9 := 2 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/stake.move:348:32+23
    assume {:print "$at(129,15845,15868)"} true;
    $t9 := 2;
    assume $IsValid'u64'($t9);

    // $t10 := ==($t8, $t9) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/stake.move:348:29+2
    $t10 := $IsEqual'u64'($t8, $t9);

    // if ($t10) goto L1 else goto L0 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/stake.move:348:13+98
    if ($t10) { goto L1; } else { goto L0; }

    // label L1 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/stake.move:348:13+98
L1:

    // $t11 := true at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/stake.move:348:13+98
    assume {:print "$at(129,15826,15924)"} true;
    $t11 := true;
    assume $IsValid'bool'($t11);

    // $t1 := $t11 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/stake.move:348:13+98
    $t1 := $t11;

    // goto L2 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/stake.move:348:13+98
    goto L2;

    // label L0 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/stake.move:348:59+15
L0:

    // $t12 := 3 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/stake.move:348:78+33
    assume {:print "$at(129,15891,15924)"} true;
    $t12 := 3;
    assume $IsValid'u64'($t12);

    // $t1 := ==($t8, $t12) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/stake.move:348:75+2
    $t1 := $IsEqual'u64'($t8, $t12);

    // label L2 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/stake.move:348:13+98
L2:

    // if ($t1) goto L4 else goto L3 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/stake.move:348:9+400
    assume {:print "$at(129,15822,16222)"} true;
    if ($t1) { goto L4; } else { goto L3; }

    // label L4 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/stake.move:349:70+12
    assume {:print "$at(129,15997,16009)"} true;
L4:

    // $t13 := get_global<stake::StakePool>($t0) on_abort goto L7 with $t6 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/stake.move:349:45+13
    assume {:print "$at(129,15972,15985)"} true;
    if (!$ResourceExists($1_stake_StakePool_$memory, $t0)) {
        call $ExecFailureAbort();
    } else {
        $t13 := $ResourceValue($1_stake_StakePool_$memory, $t0);
    }
    if ($abort_flag) {
        assume {:print "$at(129,15972,15985)"} true;
        $t6 := $abort_code;
        assume {:print "$track_abort(38,15):", $t6} $t6 == $t6;
        goto L7;
    }

    // $t14 := get_field<stake::StakePool>.active($t13) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/stake.move:349:44+46
    $t14 := $active#$1_stake_StakePool($t13);

    // $t15 := coin::value<aptos_coin::AptosCoin>($t14) on_abort goto L7 with $t6 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/stake.move:349:32+59
    call $t15 := $1_coin_value'$1_aptos_coin_AptosCoin'($t14);
    if ($abort_flag) {
        assume {:print "$at(129,15959,16018)"} true;
        $t6 := $abort_code;
        assume {:print "$track_abort(38,15):", $t6} $t6 == $t6;
        goto L7;
    }

    // trace_local[active_stake]($t15) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/stake.move:349:17+12
    assume {:print "$track_local(38,15,3):", $t15} $t15 == $t15;

    // $t16 := get_global<stake::StakePool>($t0) on_abort goto L7 with $t6 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/stake.move:350:55+13
    assume {:print "$at(129,16074,16087)"} true;
    if (!$ResourceExists($1_stake_StakePool_$memory, $t0)) {
        call $ExecFailureAbort();
    } else {
        $t16 := $ResourceValue($1_stake_StakePool_$memory, $t0);
    }
    if ($abort_flag) {
        assume {:print "$at(129,16074,16087)"} true;
        $t6 := $abort_code;
        assume {:print "$track_abort(38,15):", $t6} $t6 == $t6;
        goto L7;
    }

    // $t17 := get_field<stake::StakePool>.pending_inactive($t16) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/stake.move:350:54+56
    $t17 := $pending_inactive#$1_stake_StakePool($t16);

    // $t18 := coin::value<aptos_coin::AptosCoin>($t17) on_abort goto L7 with $t6 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/stake.move:350:42+69
    call $t18 := $1_coin_value'$1_aptos_coin_AptosCoin'($t17);
    if ($abort_flag) {
        assume {:print "$at(129,16061,16130)"} true;
        $t6 := $abort_code;
        assume {:print "$track_abort(38,15):", $t6} $t6 == $t6;
        goto L7;
    }

    // trace_local[pending_inactive_stake]($t18) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/stake.move:350:17+22
    assume {:print "$track_local(38,15,4):", $t18} $t18 == $t18;

    // $t2 := +($t15, $t18) on_abort goto L7 with $t6 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/stake.move:351:26+1
    assume {:print "$at(129,16157,16158)"} true;
    call $t2 := $AddU64($t15, $t18);
    if ($abort_flag) {
        assume {:print "$at(129,16157,16158)"} true;
        $t6 := $abort_code;
        assume {:print "$track_abort(38,15):", $t6} $t6 == $t6;
        goto L7;
    }

    // goto L5 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/stake.move:348:9+400
    assume {:print "$at(129,15822,16222)"} true;
    goto L5;

    // label L3 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/stake.move:353:13+1
    assume {:print "$at(129,16211,16212)"} true;
L3:

    // $t19 := 0 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/stake.move:353:13+1
    assume {:print "$at(129,16211,16212)"} true;
    $t19 := 0;
    assume $IsValid'u64'($t19);

    // $t2 := $t19 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/stake.move:348:9+400
    assume {:print "$at(129,15822,16222)"} true;
    $t2 := $t19;

    // label L5 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/stake.move:348:9+400
L5:

    // trace_return[0]($t2) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/stake.move:348:9+400
    assume {:print "$at(129,15822,16222)"} true;
    assume {:print "$track_return(38,15,0):", $t2} $t2 == $t2;

    // label L6 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/stake.move:355:5+1
    assume {:print "$at(129,16227,16228)"} true;
L6:

    // return $t2 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/stake.move:355:5+1
    assume {:print "$at(129,16227,16228)"} true;
    $ret0 := $t2;
    return;

    // label L7 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/stake.move:355:5+1
L7:

    // abort($t6) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/stake.move:355:5+1
    assume {:print "$at(129,16227,16228)"} true;
    $abort_code := $t6;
    $abort_flag := true;
    return;

}

// fun stake::get_delegated_voter [baseline] at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/stake.move:359:5+200
procedure {:inline 1} $1_stake_get_delegated_voter(_$t0: int) returns ($ret0: int)
{
    // declare local variables
    var $t1: int;
    var $t2: $1_stake_StakePool;
    var $t3: int;
    var $t0: int;
    var $temp_0'address': int;
    $t0 := _$t0;

    // bytecode translation starts here
    // trace_local[pool_address]($t0) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/stake.move:359:5+1
    assume {:print "$at(129,16317,16318)"} true;
    assume {:print "$track_local(38,16,0):", $t0} $t0 == $t0;

    // stake::assert_stake_pool_exists($t0) on_abort goto L2 with $t1 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/stake.move:360:9+38
    assume {:print "$at(129,16409,16447)"} true;
    call $1_stake_assert_stake_pool_exists($t0);
    if ($abort_flag) {
        assume {:print "$at(129,16409,16447)"} true;
        $t1 := $abort_code;
        assume {:print "$track_abort(38,16):", $t1} $t1 == $t1;
        goto L2;
    }

    // $t2 := get_global<stake::StakePool>($t0) on_abort goto L2 with $t1 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/stake.move:361:9+13
    assume {:print "$at(129,16457,16470)"} true;
    if (!$ResourceExists($1_stake_StakePool_$memory, $t0)) {
        call $ExecFailureAbort();
    } else {
        $t2 := $ResourceValue($1_stake_StakePool_$memory, $t0);
    }
    if ($abort_flag) {
        assume {:print "$at(129,16457,16470)"} true;
        $t1 := $abort_code;
        assume {:print "$track_abort(38,16):", $t1} $t1 == $t1;
        goto L2;
    }

    // $t3 := get_field<stake::StakePool>.delegated_voter($t2) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/stake.move:361:9+54
    $t3 := $delegated_voter#$1_stake_StakePool($t2);

    // trace_return[0]($t3) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/stake.move:361:9+54
    assume {:print "$track_return(38,16,0):", $t3} $t3 == $t3;

    // label L1 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/stake.move:362:5+1
    assume {:print "$at(129,16516,16517)"} true;
L1:

    // return $t3 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/stake.move:362:5+1
    assume {:print "$at(129,16516,16517)"} true;
    $ret0 := $t3;
    return;

    // label L2 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/stake.move:362:5+1
L2:

    // abort($t1) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/stake.move:362:5+1
    assume {:print "$at(129,16516,16517)"} true;
    $abort_code := $t1;
    $abort_flag := true;
    return;

}

// fun stake::get_lockup_secs [baseline] at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/stake.move:294:5+194
procedure {:inline 1} $1_stake_get_lockup_secs(_$t0: int) returns ($ret0: int)
{
    // declare local variables
    var $t1: int;
    var $t2: $1_stake_StakePool;
    var $t3: int;
    var $t0: int;
    var $temp_0'address': int;
    var $temp_0'u64': int;
    $t0 := _$t0;

    // bytecode translation starts here
    // trace_local[pool_address]($t0) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/stake.move:294:5+1
    assume {:print "$at(129,13232,13233)"} true;
    assume {:print "$track_local(38,17,0):", $t0} $t0 == $t0;

    // stake::assert_stake_pool_exists($t0) on_abort goto L2 with $t1 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/stake.move:295:9+38
    assume {:print "$at(129,13316,13354)"} true;
    call $1_stake_assert_stake_pool_exists($t0);
    if ($abort_flag) {
        assume {:print "$at(129,13316,13354)"} true;
        $t1 := $abort_code;
        assume {:print "$track_abort(38,17):", $t1} $t1 == $t1;
        goto L2;
    }

    // $t2 := get_global<stake::StakePool>($t0) on_abort goto L2 with $t1 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/stake.move:296:9+13
    assume {:print "$at(129,13364,13377)"} true;
    if (!$ResourceExists($1_stake_StakePool_$memory, $t0)) {
        call $ExecFailureAbort();
    } else {
        $t2 := $ResourceValue($1_stake_StakePool_$memory, $t0);
    }
    if ($abort_flag) {
        assume {:print "$at(129,13364,13377)"} true;
        $t1 := $abort_code;
        assume {:print "$track_abort(38,17):", $t1} $t1 == $t1;
        goto L2;
    }

    // $t3 := get_field<stake::StakePool>.locked_until_secs($t2) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/stake.move:296:9+56
    $t3 := $locked_until_secs#$1_stake_StakePool($t2);

    // trace_return[0]($t3) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/stake.move:296:9+56
    assume {:print "$track_return(38,17,0):", $t3} $t3 == $t3;

    // label L1 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/stake.move:297:5+1
    assume {:print "$at(129,13425,13426)"} true;
L1:

    // return $t3 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/stake.move:297:5+1
    assume {:print "$at(129,13425,13426)"} true;
    $ret0 := $t3;
    return;

    // label L2 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/stake.move:297:5+1
L2:

    // abort($t1) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/stake.move:297:5+1
    assume {:print "$at(129,13425,13426)"} true;
    $abort_code := $t1;
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
    var $t5: int;
    var $t6: $1_coin_Coin'$1_aptos_coin_AptosCoin';
    var $t7: int;
    var $t8: $1_coin_Coin'$1_aptos_coin_AptosCoin';
    var $t9: int;
    var $t10: $1_coin_Coin'$1_aptos_coin_AptosCoin';
    var $t11: int;
    var $t0: int;
    var $temp_0'$1_stake_StakePool': $1_stake_StakePool;
    var $temp_0'address': int;
    var $temp_0'u64': int;
    $t0 := _$t0;

    // bytecode translation starts here
    // trace_local[pool_address]($t0) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/stake.move:315:5+1
    assume {:print "$at(129,14196,14197)"} true;
    assume {:print "$track_local(38,22,0):", $t0} $t0 == $t0;

    // stake::assert_stake_pool_exists($t0) on_abort goto L2 with $t2 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/stake.move:316:9+38
    assume {:print "$at(129,14291,14329)"} true;
    call $1_stake_assert_stake_pool_exists($t0);
    if ($abort_flag) {
        assume {:print "$at(129,14291,14329)"} true;
        $t2 := $abort_code;
        assume {:print "$track_abort(38,22):", $t2} $t2 == $t2;
        goto L2;
    }

    // $t3 := get_global<stake::StakePool>($t0) on_abort goto L2 with $t2 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/stake.move:317:26+13
    assume {:print "$at(129,14356,14369)"} true;
    if (!$ResourceExists($1_stake_StakePool_$memory, $t0)) {
        call $ExecFailureAbort();
    } else {
        $t3 := $ResourceValue($1_stake_StakePool_$memory, $t0);
    }
    if ($abort_flag) {
        assume {:print "$at(129,14356,14369)"} true;
        $t2 := $abort_code;
        assume {:print "$track_abort(38,22):", $t2} $t2 == $t2;
        goto L2;
    }

    // trace_local[stake_pool]($t3) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/stake.move:317:13+10
    assume {:print "$track_local(38,22,1):", $t3} $t3 == $t3;

    // $t4 := get_field<stake::StakePool>.active($t3) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/stake.move:319:25+18
    assume {:print "$at(129,14430,14448)"} true;
    $t4 := $active#$1_stake_StakePool($t3);

    // $t5 := coin::value<aptos_coin::AptosCoin>($t4) on_abort goto L2 with $t2 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/stake.move:319:13+31
    call $t5 := $1_coin_value'$1_aptos_coin_AptosCoin'($t4);
    if ($abort_flag) {
        assume {:print "$at(129,14418,14449)"} true;
        $t2 := $abort_code;
        assume {:print "$track_abort(38,22):", $t2} $t2 == $t2;
        goto L2;
    }

    // $t6 := get_field<stake::StakePool>.inactive($t3) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/stake.move:320:25+20
    assume {:print "$at(129,14475,14495)"} true;
    $t6 := $inactive#$1_stake_StakePool($t3);

    // $t7 := coin::value<aptos_coin::AptosCoin>($t6) on_abort goto L2 with $t2 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/stake.move:320:13+33
    call $t7 := $1_coin_value'$1_aptos_coin_AptosCoin'($t6);
    if ($abort_flag) {
        assume {:print "$at(129,14463,14496)"} true;
        $t2 := $abort_code;
        assume {:print "$track_abort(38,22):", $t2} $t2 == $t2;
        goto L2;
    }

    // $t8 := get_field<stake::StakePool>.pending_active($t3) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/stake.move:321:25+26
    assume {:print "$at(129,14522,14548)"} true;
    $t8 := $pending_active#$1_stake_StakePool($t3);

    // $t9 := coin::value<aptos_coin::AptosCoin>($t8) on_abort goto L2 with $t2 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/stake.move:321:13+39
    call $t9 := $1_coin_value'$1_aptos_coin_AptosCoin'($t8);
    if ($abort_flag) {
        assume {:print "$at(129,14510,14549)"} true;
        $t2 := $abort_code;
        assume {:print "$track_abort(38,22):", $t2} $t2 == $t2;
        goto L2;
    }

    // $t10 := get_field<stake::StakePool>.pending_inactive($t3) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/stake.move:322:25+28
    assume {:print "$at(129,14575,14603)"} true;
    $t10 := $pending_inactive#$1_stake_StakePool($t3);

    // $t11 := coin::value<aptos_coin::AptosCoin>($t10) on_abort goto L2 with $t2 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/stake.move:322:13+41
    call $t11 := $1_coin_value'$1_aptos_coin_AptosCoin'($t10);
    if ($abort_flag) {
        assume {:print "$at(129,14563,14604)"} true;
        $t2 := $abort_code;
        assume {:print "$track_abort(38,22):", $t2} $t2 == $t2;
        goto L2;
    }

    // trace_return[0]($t5) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/stake.move:318:9+211
    assume {:print "$at(129,14404,14615)"} true;
    assume {:print "$track_return(38,22,0):", $t5} $t5 == $t5;

    // trace_return[1]($t7) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/stake.move:318:9+211
    assume {:print "$track_return(38,22,1):", $t7} $t7 == $t7;

    // trace_return[2]($t9) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/stake.move:318:9+211
    assume {:print "$track_return(38,22,2):", $t9} $t9 == $t9;

    // trace_return[3]($t11) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/stake.move:318:9+211
    assume {:print "$track_return(38,22,3):", $t11} $t11 == $t11;

    // label L1 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/stake.move:324:5+1
    assume {:print "$at(129,14620,14621)"} true;
L1:

    // return ($t5, $t7, $t9, $t11) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/stake.move:324:5+1
    assume {:print "$at(129,14620,14621)"} true;
    $ret0 := $t5;
    $ret1 := $t7;
    $ret2 := $t9;
    $ret3 := $t11;
    return;

    // label L2 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/stake.move:324:5+1
L2:

    // abort($t2) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/stake.move:324:5+1
    assume {:print "$at(129,14620,14621)"} true;
    $abort_code := $t2;
    $abort_flag := true;
    return;

}

// fun stake::get_validator_state [baseline] at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/stake.move:328:5+652
procedure {:inline 1} $1_stake_get_validator_state(_$t0: int) returns ($ret0: int)
{
    // declare local variables
    var $t1: $1_option_Option'u64';
    var $t2: $1_option_Option'u64';
    var $t3: $1_option_Option'u64';
    var $t4: int;
    var $t5: int;
    var $t6: int;
    var $t7: $1_stake_ValidatorSet;
    var $t8: $1_stake_ValidatorSet;
    var $t9: int;
    var $t10: $1_stake_ValidatorSet;
    var $t11: int;
    var $t12: Vec ($1_stake_ValidatorInfo);
    var $t13: $1_option_Option'u64';
    var $t14: bool;
    var $t15: int;
    var $t16: Vec ($1_stake_ValidatorInfo);
    var $t17: $1_option_Option'u64';
    var $t18: bool;
    var $t19: int;
    var $t20: Vec ($1_stake_ValidatorInfo);
    var $t21: $1_option_Option'u64';
    var $t22: bool;
    var $t23: int;
    var $t24: int;
    var $t0: int;
    var $temp_0'$1_stake_ValidatorSet': $1_stake_ValidatorSet;
    var $temp_0'address': int;
    var $temp_0'u64': int;
    $t0 := _$t0;

    // bytecode translation starts here
    // assume Identical($t8, global<stake::ValidatorSet>(1)) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/stake.spec.move:239:9+59
    assume {:print "$at(130,10286,10345)"} true;
    assume ($t8 == $ResourceValue($1_stake_ValidatorSet_$memory, 1));

    // trace_local[pool_address]($t0) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/stake.move:328:5+1
    assume {:print "$at(129,14678,14679)"} true;
    assume {:print "$track_local(38,25,0):", $t0} $t0 == $t0;

    // $t9 := 0x1 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/stake.move:329:57+16
    assume {:print "$at(129,14817,14833)"} true;
    $t9 := 1;
    assume $IsValid'address'($t9);

    // $t10 := get_global<stake::ValidatorSet>($t9) on_abort goto L10 with $t11 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/stake.move:329:29+13
    if (!$ResourceExists($1_stake_ValidatorSet_$memory, $t9)) {
        call $ExecFailureAbort();
    } else {
        $t10 := $ResourceValue($1_stake_ValidatorSet_$memory, $t9);
    }
    if ($abort_flag) {
        assume {:print "$at(129,14789,14802)"} true;
        $t11 := $abort_code;
        assume {:print "$track_abort(38,25):", $t11} $t11 == $t11;
        goto L10;
    }

    // trace_local[validator_set]($t10) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/stake.move:329:13+13
    assume {:print "$track_local(38,25,7):", $t10} $t10 == $t10;

    // $t12 := get_field<stake::ValidatorSet>.pending_active($t10) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/stake.move:330:45+29
    assume {:print "$at(129,14880,14909)"} true;
    $t12 := $pending_active#$1_stake_ValidatorSet($t10);

    // $t13 := opaque begin: stake::find_validator($t12, $t0) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/stake.move:330:30+59

    // assume And(WellFormed($t13), Le(Len<u64>(select option::Option.vec($t13)), 1)) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/stake.move:330:30+59
    assume ($IsValid'$1_option_Option'u64''($t13) && (LenVec($vec#$1_option_Option'u64'($t13)) <= 1));

    // assume Implies(option::$is_none<u64>($t13), forall i: Range(0, Len<stake::ValidatorInfo>($t12)): Neq<address>(select stake::ValidatorInfo.addr(Index($t12, i)), $t0)) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/stake.move:330:30+59
    assume ($1_option_$is_none'u64'($t13) ==> (var $range_0 := $Range(0, LenVec($t12)); (forall $i_1: int :: $InRange($range_0, $i_1) ==> (var i := $i_1;
    (!$IsEqual'address'($addr#$1_stake_ValidatorInfo(ReadVec($t12, i)), $t0))))));

    // assume Implies(option::$is_some<u64>($t13), Eq<address>(select stake::ValidatorInfo.addr(Index($t12, option::$borrow<u64>($t13))), $t0)) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/stake.move:330:30+59
    assume ($1_option_$is_some'u64'($t13) ==> $IsEqual'address'($addr#$1_stake_ValidatorInfo(ReadVec($t12, $1_option_$borrow'u64'($t13))), $t0));

    // assume Implies(option::$is_some<u64>($t13), stake::spec_contains($t12, $t0)) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/stake.move:330:30+59
    assume ($1_option_$is_some'u64'($t13) ==> $1_stake_spec_contains($t12, $t0));

    // $t13 := opaque end: stake::find_validator($t12, $t0) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/stake.move:330:30+59

    // $t14 := opaque begin: option::is_some<u64>($t13) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/stake.move:330:13+77

    // assume WellFormed($t14) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/stake.move:330:13+77
    assume $IsValid'bool'($t14);

    // assume Eq<bool>($t14, option::spec_is_some<u64>($t13)) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/stake.move:330:13+77
    assume $IsEqual'bool'($t14, $1_option_spec_is_some'u64'($t13));

    // $t14 := opaque end: option::is_some<u64>($t13) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/stake.move:330:13+77

    // if ($t14) goto L1 else goto L0 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/stake.move:330:9+480
    if ($t14) { goto L1; } else { goto L0; }

    // label L1 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/stake.move:330:9+480
L1:

    // $t15 := 1 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/stake.move:331:13+31
    assume {:print "$at(129,14941,14972)"} true;
    $t15 := 1;
    assume $IsValid'u64'($t15);

    // $t6 := $t15 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/stake.move:330:9+480
    assume {:print "$at(129,14844,15324)"} true;
    $t6 := $t15;

    // goto L2 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/stake.move:330:9+480
    goto L2;

    // label L0 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/stake.move:332:53+13
    assume {:print "$at(129,15025,15038)"} true;
L0:

    // $t16 := get_field<stake::ValidatorSet>.active_validators($t10) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/stake.move:332:52+32
    assume {:print "$at(129,15024,15056)"} true;
    $t16 := $active_validators#$1_stake_ValidatorSet($t10);

    // $t17 := opaque begin: stake::find_validator($t16, $t0) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/stake.move:332:37+62

    // assume And(WellFormed($t17), Le(Len<u64>(select option::Option.vec($t17)), 1)) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/stake.move:332:37+62
    assume ($IsValid'$1_option_Option'u64''($t17) && (LenVec($vec#$1_option_Option'u64'($t17)) <= 1));

    // assume Implies(option::$is_none<u64>($t17), forall i: Range(0, Len<stake::ValidatorInfo>($t16)): Neq<address>(select stake::ValidatorInfo.addr(Index($t16, i)), $t0)) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/stake.move:332:37+62
    assume ($1_option_$is_none'u64'($t17) ==> (var $range_0 := $Range(0, LenVec($t16)); (forall $i_1: int :: $InRange($range_0, $i_1) ==> (var i := $i_1;
    (!$IsEqual'address'($addr#$1_stake_ValidatorInfo(ReadVec($t16, i)), $t0))))));

    // assume Implies(option::$is_some<u64>($t17), Eq<address>(select stake::ValidatorInfo.addr(Index($t16, option::$borrow<u64>($t17))), $t0)) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/stake.move:332:37+62
    assume ($1_option_$is_some'u64'($t17) ==> $IsEqual'address'($addr#$1_stake_ValidatorInfo(ReadVec($t16, $1_option_$borrow'u64'($t17))), $t0));

    // assume Implies(option::$is_some<u64>($t17), stake::spec_contains($t16, $t0)) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/stake.move:332:37+62
    assume ($1_option_$is_some'u64'($t17) ==> $1_stake_spec_contains($t16, $t0));

    // $t17 := opaque end: stake::find_validator($t16, $t0) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/stake.move:332:37+62

    // $t18 := opaque begin: option::is_some<u64>($t17) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/stake.move:332:20+80

    // assume WellFormed($t18) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/stake.move:332:20+80
    assume $IsValid'bool'($t18);

    // assume Eq<bool>($t18, option::spec_is_some<u64>($t17)) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/stake.move:332:20+80
    assume $IsEqual'bool'($t18, $1_option_spec_is_some'u64'($t17));

    // $t18 := opaque end: option::is_some<u64>($t17) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/stake.move:332:20+80

    // if ($t18) goto L4 else goto L3 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/stake.move:332:16+336
    if ($t18) { goto L4; } else { goto L3; }

    // label L4 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/stake.move:332:16+336
L4:

    // $t19 := 2 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/stake.move:333:13+23
    assume {:print "$at(129,15088,15111)"} true;
    $t19 := 2;
    assume $IsValid'u64'($t19);

    // $t5 := $t19 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/stake.move:332:16+336
    assume {:print "$at(129,14988,15324)"} true;
    $t5 := $t19;

    // goto L5 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/stake.move:332:16+336
    goto L5;

    // label L3 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/stake.move:334:53+13
    assume {:print "$at(129,15164,15177)"} true;
L3:

    // $t20 := get_field<stake::ValidatorSet>.pending_inactive($t10) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/stake.move:334:52+31
    assume {:print "$at(129,15163,15194)"} true;
    $t20 := $pending_inactive#$1_stake_ValidatorSet($t10);

    // $t21 := opaque begin: stake::find_validator($t20, $t0) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/stake.move:334:37+61

    // assume And(WellFormed($t21), Le(Len<u64>(select option::Option.vec($t21)), 1)) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/stake.move:334:37+61
    assume ($IsValid'$1_option_Option'u64''($t21) && (LenVec($vec#$1_option_Option'u64'($t21)) <= 1));

    // assume Implies(option::$is_none<u64>($t21), forall i: Range(0, Len<stake::ValidatorInfo>($t20)): Neq<address>(select stake::ValidatorInfo.addr(Index($t20, i)), $t0)) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/stake.move:334:37+61
    assume ($1_option_$is_none'u64'($t21) ==> (var $range_0 := $Range(0, LenVec($t20)); (forall $i_1: int :: $InRange($range_0, $i_1) ==> (var i := $i_1;
    (!$IsEqual'address'($addr#$1_stake_ValidatorInfo(ReadVec($t20, i)), $t0))))));

    // assume Implies(option::$is_some<u64>($t21), Eq<address>(select stake::ValidatorInfo.addr(Index($t20, option::$borrow<u64>($t21))), $t0)) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/stake.move:334:37+61
    assume ($1_option_$is_some'u64'($t21) ==> $IsEqual'address'($addr#$1_stake_ValidatorInfo(ReadVec($t20, $1_option_$borrow'u64'($t21))), $t0));

    // assume Implies(option::$is_some<u64>($t21), stake::spec_contains($t20, $t0)) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/stake.move:334:37+61
    assume ($1_option_$is_some'u64'($t21) ==> $1_stake_spec_contains($t20, $t0));

    // $t21 := opaque end: stake::find_validator($t20, $t0) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/stake.move:334:37+61

    // $t22 := opaque begin: option::is_some<u64>($t21) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/stake.move:334:20+79

    // assume WellFormed($t22) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/stake.move:334:20+79
    assume $IsValid'bool'($t22);

    // assume Eq<bool>($t22, option::spec_is_some<u64>($t21)) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/stake.move:334:20+79
    assume $IsEqual'bool'($t22, $1_option_spec_is_some'u64'($t21));

    // $t22 := opaque end: option::is_some<u64>($t21) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/stake.move:334:20+79

    // if ($t22) goto L7 else goto L6 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/stake.move:334:16+197
    if ($t22) { goto L7; } else { goto L6; }

    // label L7 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/stake.move:335:13+33
    assume {:print "$at(129,15226,15259)"} true;
L7:

    // $t23 := 3 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/stake.move:335:13+33
    assume {:print "$at(129,15226,15259)"} true;
    $t23 := 3;
    assume $IsValid'u64'($t23);

    // $t4 := $t23 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/stake.move:334:16+197
    assume {:print "$at(129,15127,15324)"} true;
    $t4 := $t23;

    // goto L8 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/stake.move:334:16+197
    goto L8;

    // label L6 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/stake.move:337:13+25
    assume {:print "$at(129,15289,15314)"} true;
L6:

    // $t24 := 4 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/stake.move:337:13+25
    assume {:print "$at(129,15289,15314)"} true;
    $t24 := 4;
    assume $IsValid'u64'($t24);

    // $t4 := $t24 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/stake.move:334:16+197
    assume {:print "$at(129,15127,15324)"} true;
    $t4 := $t24;

    // label L8 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/stake.move:334:16+197
L8:

    // $t5 := $t4 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/stake.move:332:16+336
    assume {:print "$at(129,14988,15324)"} true;
    $t5 := $t4;

    // label L5 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/stake.move:332:16+336
L5:

    // $t6 := $t5 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/stake.move:330:9+480
    assume {:print "$at(129,14844,15324)"} true;
    $t6 := $t5;

    // label L2 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/stake.move:330:9+480
L2:

    // trace_return[0]($t6) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/stake.move:330:9+480
    assume {:print "$at(129,14844,15324)"} true;
    assume {:print "$track_return(38,25,0):", $t6} $t6 == $t6;

    // label L9 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/stake.move:339:5+1
    assume {:print "$at(129,15329,15330)"} true;
L9:

    // return $t6 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/stake.move:339:5+1
    assume {:print "$at(129,15329,15330)"} true;
    $ret0 := $t6;
    return;

    // label L10 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/stake.move:339:5+1
L10:

    // abort($t11) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/stake.move:339:5+1
    assume {:print "$at(129,15329,15330)"} true;
    $abort_code := $t11;
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
    assume {:print "$at(129,18212,18213)"} true;
    assume {:print "$track_local(38,47,0):", $t0} $t0 == $t0;

    // $t1 := exists<stake::StakePool>($t0) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/stake.move:401:9+6
    assume {:print "$at(129,18272,18278)"} true;
    $t1 := $ResourceExists($1_stake_StakePool_$memory, $t0);

    // trace_return[0]($t1) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/stake.move:401:9+23
    assume {:print "$track_return(38,47,0):", $t1} $t1 == $t1;

    // label L1 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/stake.move:402:5+1
    assume {:print "$at(129,18300,18301)"} true;
L1:

    // return $t1 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/stake.move:402:5+1
    assume {:print "$at(129,18300,18301)"} true;
    $ret0 := $t1;
    return;

}

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

// fun governance_proposal::create_proposal [baseline] at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/governance_proposal.move:10:5+94
procedure {:inline 1} $1_governance_proposal_create_proposal() returns ($ret0: $1_governance_proposal_GovernanceProposal)
{
    // declare local variables
    var $t0: bool;
    var $t1: $1_governance_proposal_GovernanceProposal;
    var $temp_0'$1_governance_proposal_GovernanceProposal': $1_governance_proposal_GovernanceProposal;

    // bytecode translation starts here
    // $t0 := false at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/governance_proposal.move:11:9+21
    assume {:print "$at(114,533,554)"} true;
    $t0 := false;
    assume $IsValid'bool'($t0);

    // $t1 := pack governance_proposal::GovernanceProposal($t0) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/governance_proposal.move:11:9+21
    $t1 := $1_governance_proposal_GovernanceProposal($t0);

    // trace_return[0]($t1) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/governance_proposal.move:11:9+21
    assume {:print "$track_return(43,1,0):", $t1} $t1 == $t1;

    // label L1 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/governance_proposal.move:12:5+1
    assume {:print "$at(114,559,560)"} true;
L1:

    // return $t1 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/governance_proposal.move:12:5+1
    assume {:print "$at(114,559,560)"} true;
    $ret0 := $t1;
    return;

}

// struct aptos_governance::CreateProposalEvent at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:100:5+226
type {:datatype} $1_aptos_governance_CreateProposalEvent;
function {:constructor} $1_aptos_governance_CreateProposalEvent($proposer: int, $stake_pool: int, $proposal_id: int, $execution_hash: Vec (int), $proposal_metadata: Table int (Vec (int))): $1_aptos_governance_CreateProposalEvent;
function {:inline} $Update'$1_aptos_governance_CreateProposalEvent'_proposer(s: $1_aptos_governance_CreateProposalEvent, x: int): $1_aptos_governance_CreateProposalEvent {
    $1_aptos_governance_CreateProposalEvent(x, $stake_pool#$1_aptos_governance_CreateProposalEvent(s), $proposal_id#$1_aptos_governance_CreateProposalEvent(s), $execution_hash#$1_aptos_governance_CreateProposalEvent(s), $proposal_metadata#$1_aptos_governance_CreateProposalEvent(s))
}
function {:inline} $Update'$1_aptos_governance_CreateProposalEvent'_stake_pool(s: $1_aptos_governance_CreateProposalEvent, x: int): $1_aptos_governance_CreateProposalEvent {
    $1_aptos_governance_CreateProposalEvent($proposer#$1_aptos_governance_CreateProposalEvent(s), x, $proposal_id#$1_aptos_governance_CreateProposalEvent(s), $execution_hash#$1_aptos_governance_CreateProposalEvent(s), $proposal_metadata#$1_aptos_governance_CreateProposalEvent(s))
}
function {:inline} $Update'$1_aptos_governance_CreateProposalEvent'_proposal_id(s: $1_aptos_governance_CreateProposalEvent, x: int): $1_aptos_governance_CreateProposalEvent {
    $1_aptos_governance_CreateProposalEvent($proposer#$1_aptos_governance_CreateProposalEvent(s), $stake_pool#$1_aptos_governance_CreateProposalEvent(s), x, $execution_hash#$1_aptos_governance_CreateProposalEvent(s), $proposal_metadata#$1_aptos_governance_CreateProposalEvent(s))
}
function {:inline} $Update'$1_aptos_governance_CreateProposalEvent'_execution_hash(s: $1_aptos_governance_CreateProposalEvent, x: Vec (int)): $1_aptos_governance_CreateProposalEvent {
    $1_aptos_governance_CreateProposalEvent($proposer#$1_aptos_governance_CreateProposalEvent(s), $stake_pool#$1_aptos_governance_CreateProposalEvent(s), $proposal_id#$1_aptos_governance_CreateProposalEvent(s), x, $proposal_metadata#$1_aptos_governance_CreateProposalEvent(s))
}
function {:inline} $Update'$1_aptos_governance_CreateProposalEvent'_proposal_metadata(s: $1_aptos_governance_CreateProposalEvent, x: Table int (Vec (int))): $1_aptos_governance_CreateProposalEvent {
    $1_aptos_governance_CreateProposalEvent($proposer#$1_aptos_governance_CreateProposalEvent(s), $stake_pool#$1_aptos_governance_CreateProposalEvent(s), $proposal_id#$1_aptos_governance_CreateProposalEvent(s), $execution_hash#$1_aptos_governance_CreateProposalEvent(s), x)
}
function $IsValid'$1_aptos_governance_CreateProposalEvent'(s: $1_aptos_governance_CreateProposalEvent): bool {
    $IsValid'address'($proposer#$1_aptos_governance_CreateProposalEvent(s))
      && $IsValid'address'($stake_pool#$1_aptos_governance_CreateProposalEvent(s))
      && $IsValid'u64'($proposal_id#$1_aptos_governance_CreateProposalEvent(s))
      && $IsValid'vec'u8''($execution_hash#$1_aptos_governance_CreateProposalEvent(s))
      && $IsValid'$1_simple_map_SimpleMap'$1_string_String_vec'u8'''($proposal_metadata#$1_aptos_governance_CreateProposalEvent(s))
}
function {:inline} $IsEqual'$1_aptos_governance_CreateProposalEvent'(s1: $1_aptos_governance_CreateProposalEvent, s2: $1_aptos_governance_CreateProposalEvent): bool {
    $IsEqual'address'($proposer#$1_aptos_governance_CreateProposalEvent(s1), $proposer#$1_aptos_governance_CreateProposalEvent(s2))
    && $IsEqual'address'($stake_pool#$1_aptos_governance_CreateProposalEvent(s1), $stake_pool#$1_aptos_governance_CreateProposalEvent(s2))
    && $IsEqual'u64'($proposal_id#$1_aptos_governance_CreateProposalEvent(s1), $proposal_id#$1_aptos_governance_CreateProposalEvent(s2))
    && $IsEqual'vec'u8''($execution_hash#$1_aptos_governance_CreateProposalEvent(s1), $execution_hash#$1_aptos_governance_CreateProposalEvent(s2))
    && $IsEqual'$1_simple_map_SimpleMap'$1_string_String_vec'u8'''($proposal_metadata#$1_aptos_governance_CreateProposalEvent(s1), $proposal_metadata#$1_aptos_governance_CreateProposalEvent(s2))}

// struct aptos_governance::VoteEvent at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:109:5+170
type {:datatype} $1_aptos_governance_VoteEvent;
function {:constructor} $1_aptos_governance_VoteEvent($proposal_id: int, $voter: int, $stake_pool: int, $num_votes: int, $should_pass: bool): $1_aptos_governance_VoteEvent;
function {:inline} $Update'$1_aptos_governance_VoteEvent'_proposal_id(s: $1_aptos_governance_VoteEvent, x: int): $1_aptos_governance_VoteEvent {
    $1_aptos_governance_VoteEvent(x, $voter#$1_aptos_governance_VoteEvent(s), $stake_pool#$1_aptos_governance_VoteEvent(s), $num_votes#$1_aptos_governance_VoteEvent(s), $should_pass#$1_aptos_governance_VoteEvent(s))
}
function {:inline} $Update'$1_aptos_governance_VoteEvent'_voter(s: $1_aptos_governance_VoteEvent, x: int): $1_aptos_governance_VoteEvent {
    $1_aptos_governance_VoteEvent($proposal_id#$1_aptos_governance_VoteEvent(s), x, $stake_pool#$1_aptos_governance_VoteEvent(s), $num_votes#$1_aptos_governance_VoteEvent(s), $should_pass#$1_aptos_governance_VoteEvent(s))
}
function {:inline} $Update'$1_aptos_governance_VoteEvent'_stake_pool(s: $1_aptos_governance_VoteEvent, x: int): $1_aptos_governance_VoteEvent {
    $1_aptos_governance_VoteEvent($proposal_id#$1_aptos_governance_VoteEvent(s), $voter#$1_aptos_governance_VoteEvent(s), x, $num_votes#$1_aptos_governance_VoteEvent(s), $should_pass#$1_aptos_governance_VoteEvent(s))
}
function {:inline} $Update'$1_aptos_governance_VoteEvent'_num_votes(s: $1_aptos_governance_VoteEvent, x: int): $1_aptos_governance_VoteEvent {
    $1_aptos_governance_VoteEvent($proposal_id#$1_aptos_governance_VoteEvent(s), $voter#$1_aptos_governance_VoteEvent(s), $stake_pool#$1_aptos_governance_VoteEvent(s), x, $should_pass#$1_aptos_governance_VoteEvent(s))
}
function {:inline} $Update'$1_aptos_governance_VoteEvent'_should_pass(s: $1_aptos_governance_VoteEvent, x: bool): $1_aptos_governance_VoteEvent {
    $1_aptos_governance_VoteEvent($proposal_id#$1_aptos_governance_VoteEvent(s), $voter#$1_aptos_governance_VoteEvent(s), $stake_pool#$1_aptos_governance_VoteEvent(s), $num_votes#$1_aptos_governance_VoteEvent(s), x)
}
function $IsValid'$1_aptos_governance_VoteEvent'(s: $1_aptos_governance_VoteEvent): bool {
    $IsValid'u64'($proposal_id#$1_aptos_governance_VoteEvent(s))
      && $IsValid'address'($voter#$1_aptos_governance_VoteEvent(s))
      && $IsValid'address'($stake_pool#$1_aptos_governance_VoteEvent(s))
      && $IsValid'u64'($num_votes#$1_aptos_governance_VoteEvent(s))
      && $IsValid'bool'($should_pass#$1_aptos_governance_VoteEvent(s))
}
function {:inline} $IsEqual'$1_aptos_governance_VoteEvent'(s1: $1_aptos_governance_VoteEvent, s2: $1_aptos_governance_VoteEvent): bool {
    s1 == s2
}

// struct aptos_governance::GovernanceConfig at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:70:5+148
type {:datatype} $1_aptos_governance_GovernanceConfig;
function {:constructor} $1_aptos_governance_GovernanceConfig($min_voting_threshold: int, $required_proposer_stake: int, $voting_duration_secs: int): $1_aptos_governance_GovernanceConfig;
function {:inline} $Update'$1_aptos_governance_GovernanceConfig'_min_voting_threshold(s: $1_aptos_governance_GovernanceConfig, x: int): $1_aptos_governance_GovernanceConfig {
    $1_aptos_governance_GovernanceConfig(x, $required_proposer_stake#$1_aptos_governance_GovernanceConfig(s), $voting_duration_secs#$1_aptos_governance_GovernanceConfig(s))
}
function {:inline} $Update'$1_aptos_governance_GovernanceConfig'_required_proposer_stake(s: $1_aptos_governance_GovernanceConfig, x: int): $1_aptos_governance_GovernanceConfig {
    $1_aptos_governance_GovernanceConfig($min_voting_threshold#$1_aptos_governance_GovernanceConfig(s), x, $voting_duration_secs#$1_aptos_governance_GovernanceConfig(s))
}
function {:inline} $Update'$1_aptos_governance_GovernanceConfig'_voting_duration_secs(s: $1_aptos_governance_GovernanceConfig, x: int): $1_aptos_governance_GovernanceConfig {
    $1_aptos_governance_GovernanceConfig($min_voting_threshold#$1_aptos_governance_GovernanceConfig(s), $required_proposer_stake#$1_aptos_governance_GovernanceConfig(s), x)
}
function $IsValid'$1_aptos_governance_GovernanceConfig'(s: $1_aptos_governance_GovernanceConfig): bool {
    $IsValid'u128'($min_voting_threshold#$1_aptos_governance_GovernanceConfig(s))
      && $IsValid'u64'($required_proposer_stake#$1_aptos_governance_GovernanceConfig(s))
      && $IsValid'u64'($voting_duration_secs#$1_aptos_governance_GovernanceConfig(s))
}
function {:inline} $IsEqual'$1_aptos_governance_GovernanceConfig'(s1: $1_aptos_governance_GovernanceConfig, s2: $1_aptos_governance_GovernanceConfig): bool {
    s1 == s2
}
var $1_aptos_governance_GovernanceConfig_$memory: $Memory $1_aptos_governance_GovernanceConfig;

// struct aptos_governance::GovernanceEvents at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:93:5+212
type {:datatype} $1_aptos_governance_GovernanceEvents;
function {:constructor} $1_aptos_governance_GovernanceEvents($create_proposal_events: $1_event_EventHandle'$1_aptos_governance_CreateProposalEvent', $update_config_events: $1_event_EventHandle'$1_aptos_governance_UpdateConfigEvent', $vote_events: $1_event_EventHandle'$1_aptos_governance_VoteEvent'): $1_aptos_governance_GovernanceEvents;
function {:inline} $Update'$1_aptos_governance_GovernanceEvents'_create_proposal_events(s: $1_aptos_governance_GovernanceEvents, x: $1_event_EventHandle'$1_aptos_governance_CreateProposalEvent'): $1_aptos_governance_GovernanceEvents {
    $1_aptos_governance_GovernanceEvents(x, $update_config_events#$1_aptos_governance_GovernanceEvents(s), $vote_events#$1_aptos_governance_GovernanceEvents(s))
}
function {:inline} $Update'$1_aptos_governance_GovernanceEvents'_update_config_events(s: $1_aptos_governance_GovernanceEvents, x: $1_event_EventHandle'$1_aptos_governance_UpdateConfigEvent'): $1_aptos_governance_GovernanceEvents {
    $1_aptos_governance_GovernanceEvents($create_proposal_events#$1_aptos_governance_GovernanceEvents(s), x, $vote_events#$1_aptos_governance_GovernanceEvents(s))
}
function {:inline} $Update'$1_aptos_governance_GovernanceEvents'_vote_events(s: $1_aptos_governance_GovernanceEvents, x: $1_event_EventHandle'$1_aptos_governance_VoteEvent'): $1_aptos_governance_GovernanceEvents {
    $1_aptos_governance_GovernanceEvents($create_proposal_events#$1_aptos_governance_GovernanceEvents(s), $update_config_events#$1_aptos_governance_GovernanceEvents(s), x)
}
function $IsValid'$1_aptos_governance_GovernanceEvents'(s: $1_aptos_governance_GovernanceEvents): bool {
    $IsValid'$1_event_EventHandle'$1_aptos_governance_CreateProposalEvent''($create_proposal_events#$1_aptos_governance_GovernanceEvents(s))
      && $IsValid'$1_event_EventHandle'$1_aptos_governance_UpdateConfigEvent''($update_config_events#$1_aptos_governance_GovernanceEvents(s))
      && $IsValid'$1_event_EventHandle'$1_aptos_governance_VoteEvent''($vote_events#$1_aptos_governance_GovernanceEvents(s))
}
function {:inline} $IsEqual'$1_aptos_governance_GovernanceEvents'(s1: $1_aptos_governance_GovernanceEvents, s2: $1_aptos_governance_GovernanceEvents): bool {
    s1 == s2
}
var $1_aptos_governance_GovernanceEvents_$memory: $Memory $1_aptos_governance_GovernanceEvents;

// struct aptos_governance::UpdateConfigEvent at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:118:5+157
type {:datatype} $1_aptos_governance_UpdateConfigEvent;
function {:constructor} $1_aptos_governance_UpdateConfigEvent($min_voting_threshold: int, $required_proposer_stake: int, $voting_duration_secs: int): $1_aptos_governance_UpdateConfigEvent;
function {:inline} $Update'$1_aptos_governance_UpdateConfigEvent'_min_voting_threshold(s: $1_aptos_governance_UpdateConfigEvent, x: int): $1_aptos_governance_UpdateConfigEvent {
    $1_aptos_governance_UpdateConfigEvent(x, $required_proposer_stake#$1_aptos_governance_UpdateConfigEvent(s), $voting_duration_secs#$1_aptos_governance_UpdateConfigEvent(s))
}
function {:inline} $Update'$1_aptos_governance_UpdateConfigEvent'_required_proposer_stake(s: $1_aptos_governance_UpdateConfigEvent, x: int): $1_aptos_governance_UpdateConfigEvent {
    $1_aptos_governance_UpdateConfigEvent($min_voting_threshold#$1_aptos_governance_UpdateConfigEvent(s), x, $voting_duration_secs#$1_aptos_governance_UpdateConfigEvent(s))
}
function {:inline} $Update'$1_aptos_governance_UpdateConfigEvent'_voting_duration_secs(s: $1_aptos_governance_UpdateConfigEvent, x: int): $1_aptos_governance_UpdateConfigEvent {
    $1_aptos_governance_UpdateConfigEvent($min_voting_threshold#$1_aptos_governance_UpdateConfigEvent(s), $required_proposer_stake#$1_aptos_governance_UpdateConfigEvent(s), x)
}
function $IsValid'$1_aptos_governance_UpdateConfigEvent'(s: $1_aptos_governance_UpdateConfigEvent): bool {
    $IsValid'u128'($min_voting_threshold#$1_aptos_governance_UpdateConfigEvent(s))
      && $IsValid'u64'($required_proposer_stake#$1_aptos_governance_UpdateConfigEvent(s))
      && $IsValid'u64'($voting_duration_secs#$1_aptos_governance_UpdateConfigEvent(s))
}
function {:inline} $IsEqual'$1_aptos_governance_UpdateConfigEvent'(s1: $1_aptos_governance_UpdateConfigEvent, s2: $1_aptos_governance_UpdateConfigEvent): bool {
    s1 == s2
}

// fun aptos_governance::create_proposal_v2 [verification] at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:229:5+3042
procedure {:timeLimit 40} $1_aptos_governance_create_proposal_v2$verify(_$t0: $signer, _$t1: int, _$t2: Vec (int), _$t3: Vec (int), _$t4: Vec (int), _$t5: bool) returns ()
{
    // declare local variables
    var $t6: int;
    var $t7: int;
    var $t8: int;
    var $t9: Vec (int);
    var $t10: Table int (Vec (int));
    var $t11: $Mutation ($1_event_EventHandle'$1_aptos_governance_CreateProposalEvent');
    var $t12: $1_option_Option'u128';
    var $t13: $1_aptos_governance_GovernanceConfig;
    var $t14: int;
    var $t15: int;
    var $t16: Table int (Vec (int));
    var $t17: int;
    var $t18: $1_option_Option'u128';
    var $t19: int;
    var $t20: int;
    var $t21: int;
    var $t22: bool;
    var $t23: int;
    var $t24: int;
    var $t25: int;
    var $t26: $1_aptos_governance_GovernanceConfig;
    var $t27: $1_staking_config_StakingConfig;
    var $t28: bool;
    var $t29: $1_stake_StakePool;
    var $t30: int;
    var $t31: int;
    var $t32: bool;
    var $t33: int;
    var $t34: int;
    var $t35: int;
    var $t36: int;
    var $t37: int;
    var $t38: int;
    var $t39: bool;
    var $t40: int;
    var $t41: int;
    var $t42: Table int (Vec (int));
    var $t43: int;
    var $t44: $1_option_Option'$1_optional_aggregator_OptionalAggregator';
    var $t45: $1_optional_aggregator_OptionalAggregator;
    var $t46: int;
    var $t47: $1_option_Option'u128';
    var $t48: $1_option_Option'u128';
    var $t49: bool;
    var $t50: int;
    var $t51: bool;
    var $t52: int;
    var $t53: int;
    var $t54: int;
    var $t55: int;
    var $t56: $1_option_Option'u128';
    var $t57: int;
    var $t58: $1_governance_proposal_GovernanceProposal;
    var $t59: int;
    var $t60: $1_voting_VotingForum'$1_governance_proposal_GovernanceProposal';
    var $t61: int;
    var $t62: $1_string_String;
    var $t63: $1_string_String;
    var $t64: int;
    var $t65: int;
    var $t66: $Mutation ($1_aptos_governance_GovernanceEvents);
    var $t67: $Mutation ($1_event_EventHandle'$1_aptos_governance_CreateProposalEvent');
    var $t68: $1_aptos_governance_CreateProposalEvent;
    var $t0: $signer;
    var $t1: int;
    var $t2: Vec (int);
    var $t3: Vec (int);
    var $t4: Vec (int);
    var $t5: bool;
    var $temp_0'$1_aptos_governance_GovernanceConfig': $1_aptos_governance_GovernanceConfig;
    var $temp_0'$1_option_Option'u128'': $1_option_Option'u128';
    var $temp_0'$1_simple_map_SimpleMap'$1_string_String_vec'u8''': Table int (Vec (int));
    var $temp_0'address': int;
    var $temp_0'bool': bool;
    var $temp_0'signer': $signer;
    var $temp_0'u64': int;
    var $temp_0'vec'u8'': Vec (int);
    $t0 := _$t0;
    $t1 := _$t1;
    $t2 := _$t2;
    $t3 := _$t3;
    $t4 := _$t4;
    $t5 := _$t5;

    // verification entrypoint assumptions
    call $InitVerification();

    // bytecode translation starts here
    // assume WellFormed($t0) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:229:5+1
    assume {:print "$at(2,9812,9813)"} true;
    assume $IsValid'signer'($t0) && $1_signer_is_txn_signer($t0) && $1_signer_is_txn_signer_addr($addr#$signer($t0));

    // assume WellFormed($t1) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:229:5+1
    assume $IsValid'address'($t1);

    // assume WellFormed($t2) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:229:5+1
    assume $IsValid'vec'u8''($t2);

    // assume WellFormed($t3) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:229:5+1
    assume $IsValid'vec'u8''($t3);

    // assume WellFormed($t4) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:229:5+1
    assume $IsValid'vec'u8''($t4);

    // assume WellFormed($t5) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:229:5+1
    assume $IsValid'bool'($t5);

    // assume forall $rsc: ResourceDomain<coin::CoinInfo<aptos_coin::AptosCoin>>(): And(WellFormed($rsc), And(Le(Len<optional_aggregator::OptionalAggregator>(select option::Option.vec(select coin::CoinInfo.supply($rsc))), 1), forall $elem: select option::Option.vec(select coin::CoinInfo.supply($rsc)): And(And(And(And(And(Iff(option::$is_some<aggregator::Aggregator>(select optional_aggregator::OptionalAggregator.aggregator($elem)), option::$is_none<optional_aggregator::Integer>(select optional_aggregator::OptionalAggregator.integer($elem))), Iff(option::$is_some<optional_aggregator::Integer>(select optional_aggregator::OptionalAggregator.integer($elem)), option::$is_none<aggregator::Aggregator>(select optional_aggregator::OptionalAggregator.aggregator($elem)))), Implies(option::$is_some<optional_aggregator::Integer>(select optional_aggregator::OptionalAggregator.integer($elem)), Le(select optional_aggregator::Integer.value(option::$borrow<optional_aggregator::Integer>(select optional_aggregator::OptionalAggregator.integer($elem))), select optional_aggregator::Integer.limit(option::$borrow<optional_aggregator::Integer>(select optional_aggregator::OptionalAggregator.integer($elem)))))), Implies(option::$is_some<aggregator::Aggregator>(select optional_aggregator::OptionalAggregator.aggregator($elem)), Le(aggregator::spec_aggregator_get_val(option::$borrow<aggregator::Aggregator>(select optional_aggregator::OptionalAggregator.aggregator($elem))), aggregator::spec_get_limit(option::$borrow<aggregator::Aggregator>(select optional_aggregator::OptionalAggregator.aggregator($elem)))))), Le(Len<aggregator::Aggregator>(select option::Option.vec(select optional_aggregator::OptionalAggregator.aggregator($elem))), 1)), Le(Len<optional_aggregator::Integer>(select option::Option.vec(select optional_aggregator::OptionalAggregator.integer($elem))), 1)))) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:229:5+1
    assume (forall $a_0: int :: {$ResourceValue($1_coin_CoinInfo'$1_aptos_coin_AptosCoin'_$memory, $a_0)}(var $rsc := $ResourceValue($1_coin_CoinInfo'$1_aptos_coin_AptosCoin'_$memory, $a_0);
    (($IsValid'$1_coin_CoinInfo'$1_aptos_coin_AptosCoin''($rsc) && ((LenVec($vec#$1_option_Option'$1_optional_aggregator_OptionalAggregator'($supply#$1_coin_CoinInfo'$1_aptos_coin_AptosCoin'($rsc))) <= 1) && (var $range_1 := $vec#$1_option_Option'$1_optional_aggregator_OptionalAggregator'($supply#$1_coin_CoinInfo'$1_aptos_coin_AptosCoin'($rsc)); (forall $i_2: int :: InRangeVec($range_1, $i_2) ==> (var $elem := ReadVec($range_1, $i_2);
    ((((((($1_option_$is_some'$1_aggregator_Aggregator'($aggregator#$1_optional_aggregator_OptionalAggregator($elem)) <==> $1_option_$is_none'$1_optional_aggregator_Integer'($integer#$1_optional_aggregator_OptionalAggregator($elem))) && ($1_option_$is_some'$1_optional_aggregator_Integer'($integer#$1_optional_aggregator_OptionalAggregator($elem)) <==> $1_option_$is_none'$1_aggregator_Aggregator'($aggregator#$1_optional_aggregator_OptionalAggregator($elem)))) && ($1_option_$is_some'$1_optional_aggregator_Integer'($integer#$1_optional_aggregator_OptionalAggregator($elem)) ==> ($value#$1_optional_aggregator_Integer($1_option_$borrow'$1_optional_aggregator_Integer'($integer#$1_optional_aggregator_OptionalAggregator($elem))) <= $limit#$1_optional_aggregator_Integer($1_option_$borrow'$1_optional_aggregator_Integer'($integer#$1_optional_aggregator_OptionalAggregator($elem)))))) && ($1_option_$is_some'$1_aggregator_Aggregator'($aggregator#$1_optional_aggregator_OptionalAggregator($elem)) ==> ($1_aggregator_spec_aggregator_get_val($1_option_$borrow'$1_aggregator_Aggregator'($aggregator#$1_optional_aggregator_OptionalAggregator($elem))) <= $1_aggregator_spec_get_limit($1_option_$borrow'$1_aggregator_Aggregator'($aggregator#$1_optional_aggregator_OptionalAggregator($elem)))))) && (LenVec($vec#$1_option_Option'$1_aggregator_Aggregator'($aggregator#$1_optional_aggregator_OptionalAggregator($elem))) <= 1)) && (LenVec($vec#$1_option_Option'$1_optional_aggregator_Integer'($integer#$1_optional_aggregator_OptionalAggregator($elem))) <= 1)))))))))));

    // assume forall $rsc: ResourceDomain<chain_status::GenesisEndMarker>(): WellFormed($rsc) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:229:5+1
    assume (forall $a_0: int :: {$ResourceValue($1_chain_status_GenesisEndMarker_$memory, $a_0)}(var $rsc := $ResourceValue($1_chain_status_GenesisEndMarker_$memory, $a_0);
    ($IsValid'$1_chain_status_GenesisEndMarker'($rsc))));

    // assume forall $rsc: ResourceDomain<timestamp::CurrentTimeMicroseconds>(): WellFormed($rsc) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:229:5+1
    assume (forall $a_0: int :: {$ResourceValue($1_timestamp_CurrentTimeMicroseconds_$memory, $a_0)}(var $rsc := $ResourceValue($1_timestamp_CurrentTimeMicroseconds_$memory, $a_0);
    ($IsValid'$1_timestamp_CurrentTimeMicroseconds'($rsc))));

    // assume forall $rsc: ResourceDomain<voting::VotingForum<governance_proposal::GovernanceProposal>>(): And(WellFormed($rsc), forall $key: select voting::VotingForum.proposals($rsc): And(Le(Len<governance_proposal::GovernanceProposal>(select option::Option.vec(select voting::Proposal.execution_content(table::spec_get<u64, voting::Proposal<governance_proposal::GovernanceProposal>>(select voting::VotingForum.proposals($rsc), $key)))), 1), Le(Len<u128>(select option::Option.vec(select voting::Proposal.early_resolution_vote_threshold(table::spec_get<u64, voting::Proposal<governance_proposal::GovernanceProposal>>(select voting::VotingForum.proposals($rsc), $key)))), 1))) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:229:5+1
    assume (forall $a_0: int :: {$ResourceValue($1_voting_VotingForum'$1_governance_proposal_GovernanceProposal'_$memory, $a_0)}(var $rsc := $ResourceValue($1_voting_VotingForum'$1_governance_proposal_GovernanceProposal'_$memory, $a_0);
    (($IsValid'$1_voting_VotingForum'$1_governance_proposal_GovernanceProposal''($rsc) && (var $range_1 := $proposals#$1_voting_VotingForum'$1_governance_proposal_GovernanceProposal'($rsc); (forall $key: int :: ContainsTable($range_1, $EncodeKey'u64'($key)) ==> (((LenVec($vec#$1_option_Option'$1_governance_proposal_GovernanceProposal'($execution_content#$1_voting_Proposal'$1_governance_proposal_GovernanceProposal'($1_table_spec_get'u64_$1_voting_Proposal'$1_governance_proposal_GovernanceProposal''($proposals#$1_voting_VotingForum'$1_governance_proposal_GovernanceProposal'($rsc), $key)))) <= 1) && (LenVec($vec#$1_option_Option'u128'($early_resolution_vote_threshold#$1_voting_Proposal'$1_governance_proposal_GovernanceProposal'($1_table_spec_get'u64_$1_voting_Proposal'$1_governance_proposal_GovernanceProposal''($proposals#$1_voting_VotingForum'$1_governance_proposal_GovernanceProposal'($rsc), $key)))) <= 1)))))))));

    // assume forall $rsc: ResourceDomain<staking_config::StakingConfig>(): And(WellFormed($rsc), And(And(Le(select staking_config::StakingConfig.rewards_rate($rsc), 1000000), Gt(select staking_config::StakingConfig.rewards_rate_denominator($rsc), 0)), Le(select staking_config::StakingConfig.rewards_rate($rsc), select staking_config::StakingConfig.rewards_rate_denominator($rsc)))) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:229:5+1
    assume (forall $a_0: int :: {$ResourceValue($1_staking_config_StakingConfig_$memory, $a_0)}(var $rsc := $ResourceValue($1_staking_config_StakingConfig_$memory, $a_0);
    (($IsValid'$1_staking_config_StakingConfig'($rsc) && ((($rewards_rate#$1_staking_config_StakingConfig($rsc) <= 1000000) && ($rewards_rate_denominator#$1_staking_config_StakingConfig($rsc) > 0)) && ($rewards_rate#$1_staking_config_StakingConfig($rsc) <= $rewards_rate_denominator#$1_staking_config_StakingConfig($rsc)))))));

    // assume forall $rsc: ResourceDomain<stake::AptosCoinCapabilities>(): WellFormed($rsc) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:229:5+1
    assume (forall $a_0: int :: {$ResourceValue($1_stake_AptosCoinCapabilities_$memory, $a_0)}(var $rsc := $ResourceValue($1_stake_AptosCoinCapabilities_$memory, $a_0);
    ($IsValid'$1_stake_AptosCoinCapabilities'($rsc))));

    // assume forall $rsc: ResourceDomain<stake::StakePool>(): WellFormed($rsc) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:229:5+1
    assume (forall $a_0: int :: {$ResourceValue($1_stake_StakePool_$memory, $a_0)}(var $rsc := $ResourceValue($1_stake_StakePool_$memory, $a_0);
    ($IsValid'$1_stake_StakePool'($rsc))));

    // assume forall $rsc: ResourceDomain<stake::ValidatorConfig>(): WellFormed($rsc) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:229:5+1
    assume (forall $a_0: int :: {$ResourceValue($1_stake_ValidatorConfig_$memory, $a_0)}(var $rsc := $ResourceValue($1_stake_ValidatorConfig_$memory, $a_0);
    ($IsValid'$1_stake_ValidatorConfig'($rsc))));

    // assume forall $rsc: ResourceDomain<stake::ValidatorPerformance>(): WellFormed($rsc) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:229:5+1
    assume (forall $a_0: int :: {$ResourceValue($1_stake_ValidatorPerformance_$memory, $a_0)}(var $rsc := $ResourceValue($1_stake_ValidatorPerformance_$memory, $a_0);
    ($IsValid'$1_stake_ValidatorPerformance'($rsc))));

    // assume forall $rsc: ResourceDomain<stake::ValidatorSet>(): WellFormed($rsc) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:229:5+1
    assume (forall $a_0: int :: {$ResourceValue($1_stake_ValidatorSet_$memory, $a_0)}(var $rsc := $ResourceValue($1_stake_ValidatorSet_$memory, $a_0);
    ($IsValid'$1_stake_ValidatorSet'($rsc))));

    // assume forall $rsc: ResourceDomain<transaction_fee::AptosCoinCapabilities>(): WellFormed($rsc) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:229:5+1
    assume (forall $a_0: int :: {$ResourceValue($1_transaction_fee_AptosCoinCapabilities_$memory, $a_0)}(var $rsc := $ResourceValue($1_transaction_fee_AptosCoinCapabilities_$memory, $a_0);
    ($IsValid'$1_transaction_fee_AptosCoinCapabilities'($rsc))));

    // assume forall $rsc: ResourceDomain<state_storage::GasParameter>(): WellFormed($rsc) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:229:5+1
    assume (forall $a_0: int :: {$ResourceValue($1_state_storage_GasParameter_$memory, $a_0)}(var $rsc := $ResourceValue($1_state_storage_GasParameter_$memory, $a_0);
    ($IsValid'$1_state_storage_GasParameter'($rsc))));

    // assume forall $rsc: ResourceDomain<state_storage::StateStorageUsage>(): WellFormed($rsc) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:229:5+1
    assume (forall $a_0: int :: {$ResourceValue($1_state_storage_StateStorageUsage_$memory, $a_0)}(var $rsc := $ResourceValue($1_state_storage_StateStorageUsage_$memory, $a_0);
    ($IsValid'$1_state_storage_StateStorageUsage'($rsc))));

    // assume forall $rsc: ResourceDomain<storage_gas::StorageGas>(): WellFormed($rsc) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:229:5+1
    assume (forall $a_0: int :: {$ResourceValue($1_storage_gas_StorageGas_$memory, $a_0)}(var $rsc := $ResourceValue($1_storage_gas_StorageGas_$memory, $a_0);
    ($IsValid'$1_storage_gas_StorageGas'($rsc))));

    // assume forall $rsc: ResourceDomain<storage_gas::StorageGasConfig>(): And(WellFormed($rsc), And(And(And(And(And(And(And(And(And(And(And(And(And(And(And(And(And(And(And(And(And(And(And(And(And(And(And(Gt(select storage_gas::UsageGasConfig.target_usage(select storage_gas::StorageGasConfig.item_config($rsc)), 0), Le(select storage_gas::UsageGasConfig.target_usage(select storage_gas::StorageGasConfig.item_config($rsc)), Div(18446744073709551615, 10000))), Le(select storage_gas::GasCurve.min_gas(select storage_gas::UsageGasConfig.read_curve(select storage_gas::StorageGasConfig.item_config($rsc))), select storage_gas::GasCurve.max_gas(select storage_gas::UsageGasConfig.read_curve(select storage_gas::StorageGasConfig.item_config($rsc))))), Le(select storage_gas::GasCurve.max_gas(select storage_gas::UsageGasConfig.read_curve(select storage_gas::StorageGasConfig.item_config($rsc))), Div(18446744073709551615, 10000))), And(And(Implies(Gt(Len<storage_gas::Point>(select storage_gas::GasCurve.points(select storage_gas::UsageGasConfig.read_curve(select storage_gas::StorageGasConfig.item_config($rsc)))), 0), Gt(select storage_gas::Point.x(Index(select storage_gas::GasCurve.points(select storage_gas::UsageGasConfig.read_curve(select storage_gas::StorageGasConfig.item_config($rsc))), 0)), 0)), Implies(Gt(Len<storage_gas::Point>(select storage_gas::GasCurve.points(select storage_gas::UsageGasConfig.read_curve(select storage_gas::StorageGasConfig.item_config($rsc)))), 0), Lt(select storage_gas::Point.x(Index(select storage_gas::GasCurve.points(select storage_gas::UsageGasConfig.read_curve(select storage_gas::StorageGasConfig.item_config($rsc))), Sub(Len<storage_gas::Point>(select storage_gas::GasCurve.points(select storage_gas::UsageGasConfig.read_curve(select storage_gas::StorageGasConfig.item_config($rsc)))), 1))), 10000))), forall i: Range(0, Sub(Len<storage_gas::Point>(select storage_gas::GasCurve.points(select storage_gas::UsageGasConfig.read_curve(select storage_gas::StorageGasConfig.item_config($rsc)))), 1)): And(Lt(select storage_gas::Point.x(Index(select storage_gas::GasCurve.points(select storage_gas::UsageGasConfig.read_curve(select storage_gas::StorageGasConfig.item_config($rsc))), i)), select storage_gas::Point.x(Index(select storage_gas::GasCurve.points(select storage_gas::UsageGasConfig.read_curve(select storage_gas::StorageGasConfig.item_config($rsc))), Add(i, 1)))), Le(select storage_gas::Point.y(Index(select storage_gas::GasCurve.points(select storage_gas::UsageGasConfig.read_curve(select storage_gas::StorageGasConfig.item_config($rsc))), i)), select storage_gas::Point.y(Index(select storage_gas::GasCurve.points(select storage_gas::UsageGasConfig.read_curve(select storage_gas::StorageGasConfig.item_config($rsc))), Add(i, 1))))))), forall $elem: select storage_gas::GasCurve.points(select storage_gas::UsageGasConfig.read_curve(select storage_gas::StorageGasConfig.item_config($rsc))): And(Le(select storage_gas::Point.x($elem), 10000), Le(select storage_gas::Point.y($elem), 10000))), Le(select storage_gas::GasCurve.min_gas(select storage_gas::UsageGasConfig.create_curve(select storage_gas::StorageGasConfig.item_config($rsc))), select storage_gas::GasCurve.max_gas(select storage_gas::UsageGasConfig.create_curve(select storage_gas::StorageGasConfig.item_config($rsc))))), Le(select storage_gas::GasCurve.max_gas(select storage_gas::UsageGasConfig.create_curve(select storage_gas::StorageGasConfig.item_config($rsc))), Div(18446744073709551615, 10000))), And(And(Implies(Gt(Len<storage_gas::Point>(select storage_gas::GasCurve.points(select storage_gas::UsageGasConfig.create_curve(select storage_gas::StorageGasConfig.item_config($rsc)))), 0), Gt(select storage_gas::Point.x(Index(select storage_gas::GasCurve.points(select storage_gas::UsageGasConfig.create_curve(select storage_gas::StorageGasConfig.item_config($rsc))), 0)), 0)), Implies(Gt(Len<storage_gas::Point>(select storage_gas::GasCurve.points(select storage_gas::UsageGasConfig.create_curve(select storage_gas::StorageGasConfig.item_config($rsc)))), 0), Lt(select storage_gas::Point.x(Index(select storage_gas::GasCurve.points(select storage_gas::UsageGasConfig.create_curve(select storage_gas::StorageGasConfig.item_config($rsc))), Sub(Len<storage_gas::Point>(select storage_gas::GasCurve.points(select storage_gas::UsageGasConfig.create_curve(select storage_gas::StorageGasConfig.item_config($rsc)))), 1))), 10000))), forall i: Range(0, Sub(Len<storage_gas::Point>(select storage_gas::GasCurve.points(select storage_gas::UsageGasConfig.create_curve(select storage_gas::StorageGasConfig.item_config($rsc)))), 1)): And(Lt(select storage_gas::Point.x(Index(select storage_gas::GasCurve.points(select storage_gas::UsageGasConfig.create_curve(select storage_gas::StorageGasConfig.item_config($rsc))), i)), select storage_gas::Point.x(Index(select storage_gas::GasCurve.points(select storage_gas::UsageGasConfig.create_curve(select storage_gas::StorageGasConfig.item_config($rsc))), Add(i, 1)))), Le(select storage_gas::Point.y(Index(select storage_gas::GasCurve.points(select storage_gas::UsageGasConfig.create_curve(select storage_gas::StorageGasConfig.item_config($rsc))), i)), select storage_gas::Point.y(Index(select storage_gas::GasCurve.points(select storage_gas::UsageGasConfig.create_curve(select storage_gas::StorageGasConfig.item_config($rsc))), Add(i, 1))))))), forall $elem: select storage_gas::GasCurve.points(select storage_gas::UsageGasConfig.create_curve(select storage_gas::StorageGasConfig.item_config($rsc))): And(Le(select storage_gas::Point.x($elem), 10000), Le(select storage_gas::Point.y($elem), 10000))), Le(select storage_gas::GasCurve.min_gas(select storage_gas::UsageGasConfig.write_curve(select storage_gas::StorageGasConfig.item_config($rsc))), select storage_gas::GasCurve.max_gas(select storage_gas::UsageGasConfig.write_curve(select storage_gas::StorageGasConfig.item_config($rsc))))), Le(select storage_gas::GasCurve.max_gas(select storage_gas::UsageGasConfig.write_curve(select storage_gas::StorageGasConfig.item_config($rsc))), Div(18446744073709551615, 10000))), And(And(Implies(Gt(Len<storage_gas::Point>(select storage_gas::GasCurve.points(select storage_gas::UsageGasConfig.write_curve(select storage_gas::StorageGasConfig.item_config($rsc)))), 0), Gt(select storage_gas::Point.x(Index(select storage_gas::GasCurve.points(select storage_gas::UsageGasConfig.write_curve(select storage_gas::StorageGasConfig.item_config($rsc))), 0)), 0)), Implies(Gt(Len<storage_gas::Point>(select storage_gas::GasCurve.points(select storage_gas::UsageGasConfig.write_curve(select storage_gas::StorageGasConfig.item_config($rsc)))), 0), Lt(select storage_gas::Point.x(Index(select storage_gas::GasCurve.points(select storage_gas::UsageGasConfig.write_curve(select storage_gas::StorageGasConfig.item_config($rsc))), Sub(Len<storage_gas::Point>(select storage_gas::GasCurve.points(select storage_gas::UsageGasConfig.write_curve(select storage_gas::StorageGasConfig.item_config($rsc)))), 1))), 10000))), forall i: Range(0, Sub(Len<storage_gas::Point>(select storage_gas::GasCurve.points(select storage_gas::UsageGasConfig.write_curve(select storage_gas::StorageGasConfig.item_config($rsc)))), 1)): And(Lt(select storage_gas::Point.x(Index(select storage_gas::GasCurve.points(select storage_gas::UsageGasConfig.write_curve(select storage_gas::StorageGasConfig.item_config($rsc))), i)), select storage_gas::Point.x(Index(select storage_gas::GasCurve.points(select storage_gas::UsageGasConfig.write_curve(select storage_gas::StorageGasConfig.item_config($rsc))), Add(i, 1)))), Le(select storage_gas::Point.y(Index(select storage_gas::GasCurve.points(select storage_gas::UsageGasConfig.write_curve(select storage_gas::StorageGasConfig.item_config($rsc))), i)), select storage_gas::Point.y(Index(select storage_gas::GasCurve.points(select storage_gas::UsageGasConfig.write_curve(select storage_gas::StorageGasConfig.item_config($rsc))), Add(i, 1))))))), forall $elem: select storage_gas::GasCurve.points(select storage_gas::UsageGasConfig.write_curve(select storage_gas::StorageGasConfig.item_config($rsc))): And(Le(select storage_gas::Point.x($elem), 10000), Le(select storage_gas::Point.y($elem), 10000))), Gt(select storage_gas::UsageGasConfig.target_usage(select storage_gas::StorageGasConfig.byte_config($rsc)), 0)), Le(select storage_gas::UsageGasConfig.target_usage(select storage_gas::StorageGasConfig.byte_config($rsc)), Div(18446744073709551615, 10000))), Le(select storage_gas::GasCurve.min_gas(select storage_gas::UsageGasConfig.read_curve(select storage_gas::StorageGasConfig.byte_config($rsc))), select storage_gas::GasCurve.max_gas(select storage_gas::UsageGasConfig.read_curve(select storage_gas::StorageGasConfig.byte_config($rsc))))), Le(select storage_gas::GasCurve.max_gas(select storage_gas::UsageGasConfig.read_curve(select storage_gas::StorageGasConfig.byte_config($rsc))), Div(18446744073709551615, 10000))), And(And(Implies(Gt(Len<storage_gas::Point>(select storage_gas::GasCurve.points(select storage_gas::UsageGasConfig.read_curve(select storage_gas::StorageGasConfig.byte_config($rsc)))), 0), Gt(select storage_gas::Point.x(Index(select storage_gas::GasCurve.points(select storage_gas::UsageGasConfig.read_curve(select storage_gas::StorageGasConfig.byte_config($rsc))), 0)), 0)), Implies(Gt(Len<storage_gas::Point>(select storage_gas::GasCurve.points(select storage_gas::UsageGasConfig.read_curve(select storage_gas::StorageGasConfig.byte_config($rsc)))), 0), Lt(select storage_gas::Point.x(Index(select storage_gas::GasCurve.points(select storage_gas::UsageGasConfig.read_curve(select storage_gas::StorageGasConfig.byte_config($rsc))), Sub(Len<storage_gas::Point>(select storage_gas::GasCurve.points(select storage_gas::UsageGasConfig.read_curve(select storage_gas::StorageGasConfig.byte_config($rsc)))), 1))), 10000))), forall i: Range(0, Sub(Len<storage_gas::Point>(select storage_gas::GasCurve.points(select storage_gas::UsageGasConfig.read_curve(select storage_gas::StorageGasConfig.byte_config($rsc)))), 1)): And(Lt(select storage_gas::Point.x(Index(select storage_gas::GasCurve.points(select storage_gas::UsageGasConfig.read_curve(select storage_gas::StorageGasConfig.byte_config($rsc))), i)), select storage_gas::Point.x(Index(select storage_gas::GasCurve.points(select storage_gas::UsageGasConfig.read_curve(select storage_gas::StorageGasConfig.byte_config($rsc))), Add(i, 1)))), Le(select storage_gas::Point.y(Index(select storage_gas::GasCurve.points(select storage_gas::UsageGasConfig.read_curve(select storage_gas::StorageGasConfig.byte_config($rsc))), i)), select storage_gas::Point.y(Index(select storage_gas::GasCurve.points(select storage_gas::UsageGasConfig.read_curve(select storage_gas::StorageGasConfig.byte_config($rsc))), Add(i, 1))))))), forall $elem: select storage_gas::GasCurve.points(select storage_gas::UsageGasConfig.read_curve(select storage_gas::StorageGasConfig.byte_config($rsc))): And(Le(select storage_gas::Point.x($elem), 10000), Le(select storage_gas::Point.y($elem), 10000))), Le(select storage_gas::GasCurve.min_gas(select storage_gas::UsageGasConfig.create_curve(select storage_gas::StorageGasConfig.byte_config($rsc))), select storage_gas::GasCurve.max_gas(select storage_gas::UsageGasConfig.create_curve(select storage_gas::StorageGasConfig.byte_config($rsc))))), Le(select storage_gas::GasCurve.max_gas(select storage_gas::UsageGasConfig.create_curve(select storage_gas::StorageGasConfig.byte_config($rsc))), Div(18446744073709551615, 10000))), And(And(Implies(Gt(Len<storage_gas::Point>(select storage_gas::GasCurve.points(select storage_gas::UsageGasConfig.create_curve(select storage_gas::StorageGasConfig.byte_config($rsc)))), 0), Gt(select storage_gas::Point.x(Index(select storage_gas::GasCurve.points(select storage_gas::UsageGasConfig.create_curve(select storage_gas::StorageGasConfig.byte_config($rsc))), 0)), 0)), Implies(Gt(Len<storage_gas::Point>(select storage_gas::GasCurve.points(select storage_gas::UsageGasConfig.create_curve(select storage_gas::StorageGasConfig.byte_config($rsc)))), 0), Lt(select storage_gas::Point.x(Index(select storage_gas::GasCurve.points(select storage_gas::UsageGasConfig.create_curve(select storage_gas::StorageGasConfig.byte_config($rsc))), Sub(Len<storage_gas::Point>(select storage_gas::GasCurve.points(select storage_gas::UsageGasConfig.create_curve(select storage_gas::StorageGasConfig.byte_config($rsc)))), 1))), 10000))), forall i: Range(0, Sub(Len<storage_gas::Point>(select storage_gas::GasCurve.points(select storage_gas::UsageGasConfig.create_curve(select storage_gas::StorageGasConfig.byte_config($rsc)))), 1)): And(Lt(select storage_gas::Point.x(Index(select storage_gas::GasCurve.points(select storage_gas::UsageGasConfig.create_curve(select storage_gas::StorageGasConfig.byte_config($rsc))), i)), select storage_gas::Point.x(Index(select storage_gas::GasCurve.points(select storage_gas::UsageGasConfig.create_curve(select storage_gas::StorageGasConfig.byte_config($rsc))), Add(i, 1)))), Le(select storage_gas::Point.y(Index(select storage_gas::GasCurve.points(select storage_gas::UsageGasConfig.create_curve(select storage_gas::StorageGasConfig.byte_config($rsc))), i)), select storage_gas::Point.y(Index(select storage_gas::GasCurve.points(select storage_gas::UsageGasConfig.create_curve(select storage_gas::StorageGasConfig.byte_config($rsc))), Add(i, 1))))))), forall $elem: select storage_gas::GasCurve.points(select storage_gas::UsageGasConfig.create_curve(select storage_gas::StorageGasConfig.byte_config($rsc))): And(Le(select storage_gas::Point.x($elem), 10000), Le(select storage_gas::Point.y($elem), 10000))), Le(select storage_gas::GasCurve.min_gas(select storage_gas::UsageGasConfig.write_curve(select storage_gas::StorageGasConfig.byte_config($rsc))), select storage_gas::GasCurve.max_gas(select storage_gas::UsageGasConfig.write_curve(select storage_gas::StorageGasConfig.byte_config($rsc))))), Le(select storage_gas::GasCurve.max_gas(select storage_gas::UsageGasConfig.write_curve(select storage_gas::StorageGasConfig.byte_config($rsc))), Div(18446744073709551615, 10000))), And(And(Implies(Gt(Len<storage_gas::Point>(select storage_gas::GasCurve.points(select storage_gas::UsageGasConfig.write_curve(select storage_gas::StorageGasConfig.byte_config($rsc)))), 0), Gt(select storage_gas::Point.x(Index(select storage_gas::GasCurve.points(select storage_gas::UsageGasConfig.write_curve(select storage_gas::StorageGasConfig.byte_config($rsc))), 0)), 0)), Implies(Gt(Len<storage_gas::Point>(select storage_gas::GasCurve.points(select storage_gas::UsageGasConfig.write_curve(select storage_gas::StorageGasConfig.byte_config($rsc)))), 0), Lt(select storage_gas::Point.x(Index(select storage_gas::GasCurve.points(select storage_gas::UsageGasConfig.write_curve(select storage_gas::StorageGasConfig.byte_config($rsc))), Sub(Len<storage_gas::Point>(select storage_gas::GasCurve.points(select storage_gas::UsageGasConfig.write_curve(select storage_gas::StorageGasConfig.byte_config($rsc)))), 1))), 10000))), forall i: Range(0, Sub(Len<storage_gas::Point>(select storage_gas::GasCurve.points(select storage_gas::UsageGasConfig.write_curve(select storage_gas::StorageGasConfig.byte_config($rsc)))), 1)): And(Lt(select storage_gas::Point.x(Index(select storage_gas::GasCurve.points(select storage_gas::UsageGasConfig.write_curve(select storage_gas::StorageGasConfig.byte_config($rsc))), i)), select storage_gas::Point.x(Index(select storage_gas::GasCurve.points(select storage_gas::UsageGasConfig.write_curve(select storage_gas::StorageGasConfig.byte_config($rsc))), Add(i, 1)))), Le(select storage_gas::Point.y(Index(select storage_gas::GasCurve.points(select storage_gas::UsageGasConfig.write_curve(select storage_gas::StorageGasConfig.byte_config($rsc))), i)), select storage_gas::Point.y(Index(select storage_gas::GasCurve.points(select storage_gas::UsageGasConfig.write_curve(select storage_gas::StorageGasConfig.byte_config($rsc))), Add(i, 1))))))), forall $elem: select storage_gas::GasCurve.points(select storage_gas::UsageGasConfig.write_curve(select storage_gas::StorageGasConfig.byte_config($rsc))): And(Le(select storage_gas::Point.x($elem), 10000), Le(select storage_gas::Point.y($elem), 10000)))) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:229:5+1
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

    // assume forall $rsc: ResourceDomain<reconfiguration::Configuration>(): WellFormed($rsc) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:229:5+1
    assume (forall $a_0: int :: {$ResourceValue($1_reconfiguration_Configuration_$memory, $a_0)}(var $rsc := $ResourceValue($1_reconfiguration_Configuration_$memory, $a_0);
    ($IsValid'$1_reconfiguration_Configuration'($rsc))));

    // assume forall $rsc: ResourceDomain<aptos_governance::GovernanceConfig>(): WellFormed($rsc) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:229:5+1
    assume (forall $a_0: int :: {$ResourceValue($1_aptos_governance_GovernanceConfig_$memory, $a_0)}(var $rsc := $ResourceValue($1_aptos_governance_GovernanceConfig_$memory, $a_0);
    ($IsValid'$1_aptos_governance_GovernanceConfig'($rsc))));

    // assume forall $rsc: ResourceDomain<aptos_governance::GovernanceEvents>(): WellFormed($rsc) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:229:5+1
    assume (forall $a_0: int :: {$ResourceValue($1_aptos_governance_GovernanceEvents_$memory, $a_0)}(var $rsc := $ResourceValue($1_aptos_governance_GovernanceEvents_$memory, $a_0);
    ($IsValid'$1_aptos_governance_GovernanceEvents'($rsc))));

    // assume forall $rsc: ResourceDomain<block::BlockResource>(): WellFormed($rsc) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:229:5+1
    assume (forall $a_0: int :: {$ResourceValue($1_block_BlockResource_$memory, $a_0)}(var $rsc := $ResourceValue($1_block_BlockResource_$memory, $a_0);
    ($IsValid'$1_block_BlockResource'($rsc))));

    // assume Implies(chain_status::$is_operating(), exists<timestamp::CurrentTimeMicroseconds>(1)) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:229:5+3042
    // global invariant at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/timestamp.spec.move:4:9+93
    assume ($1_chain_status_$is_operating($1_chain_status_GenesisEndMarker_$memory) ==> $ResourceExists($1_timestamp_CurrentTimeMicroseconds_$memory, 1));

    // assume Implies(chain_status::$is_operating(), exists<staking_config::StakingConfig>(1)) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:229:5+3042
    // global invariant at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/configs/staking_config.spec.move:4:9+83
    assume ($1_chain_status_$is_operating($1_chain_status_GenesisEndMarker_$memory) ==> $ResourceExists($1_staking_config_StakingConfig_$memory, 1));

    // assume Implies(exists<stake::ValidatorSet>(1), stake::validator_set_is_valid()) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:229:5+3042
    // global invariant at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/stake.spec.move:8:9+92
    assume ($ResourceExists($1_stake_ValidatorSet_$memory, 1) ==> $1_stake_validator_set_is_valid($1_stake_StakePool_$memory, $1_stake_ValidatorConfig_$memory, $1_stake_ValidatorPerformance_$memory, $1_stake_ValidatorSet_$memory));

    // assume Implies(chain_status::$is_operating(), exists<stake::AptosCoinCapabilities>(1)) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:229:5+3042
    // global invariant at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/stake.spec.move:10:9+105
    assume ($1_chain_status_$is_operating($1_chain_status_GenesisEndMarker_$memory) ==> $ResourceExists($1_stake_AptosCoinCapabilities_$memory, 1));

    // assume Implies(chain_status::$is_operating(), exists<stake::ValidatorPerformance>(1)) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:229:5+3042
    // global invariant at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/stake.spec.move:11:9+104
    assume ($1_chain_status_$is_operating($1_chain_status_GenesisEndMarker_$memory) ==> $ResourceExists($1_stake_ValidatorPerformance_$memory, 1));

    // assume Implies(chain_status::$is_operating(), exists<stake::ValidatorSet>(1)) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:229:5+3042
    // global invariant at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/stake.spec.move:12:9+96
    assume ($1_chain_status_$is_operating($1_chain_status_GenesisEndMarker_$memory) ==> $ResourceExists($1_stake_ValidatorSet_$memory, 1));

    // assume Implies(chain_status::$is_operating(), exists<transaction_fee::AptosCoinCapabilities>(1)) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:229:5+3042
    // global invariant at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/transaction_fee.spec.move:7:9+105
    assume ($1_chain_status_$is_operating($1_chain_status_GenesisEndMarker_$memory) ==> $ResourceExists($1_transaction_fee_AptosCoinCapabilities_$memory, 1));

    // assume Implies(chain_status::$is_operating(), exists<state_storage::StateStorageUsage>(1)) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:229:5+3042
    // global invariant at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/state_storage.spec.move:7:9+101
    assume ($1_chain_status_$is_operating($1_chain_status_GenesisEndMarker_$memory) ==> $ResourceExists($1_state_storage_StateStorageUsage_$memory, 1));

    // assume Implies(chain_status::$is_operating(), exists<state_storage::GasParameter>(1)) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:229:5+3042
    // global invariant at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/state_storage.spec.move:8:9+96
    assume ($1_chain_status_$is_operating($1_chain_status_GenesisEndMarker_$memory) ==> $ResourceExists($1_state_storage_GasParameter_$memory, 1));

    // assume Implies(chain_status::$is_operating(), exists<storage_gas::StorageGasConfig>(1)) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:229:5+3042
    // global invariant at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/storage_gas.spec.move:34:9+100
    assume ($1_chain_status_$is_operating($1_chain_status_GenesisEndMarker_$memory) ==> $ResourceExists($1_storage_gas_StorageGasConfig_$memory, 1));

    // assume Implies(chain_status::$is_operating(), exists<storage_gas::StorageGas>(1)) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:229:5+3042
    // global invariant at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/storage_gas.spec.move:35:9+94
    assume ($1_chain_status_$is_operating($1_chain_status_GenesisEndMarker_$memory) ==> $ResourceExists($1_storage_gas_StorageGas_$memory, 1));

    // assume Implies(chain_status::$is_operating(), exists<reconfiguration::Configuration>(1)) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:229:5+3042
    // global invariant at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/reconfiguration.spec.move:7:9+97
    assume ($1_chain_status_$is_operating($1_chain_status_GenesisEndMarker_$memory) ==> $ResourceExists($1_reconfiguration_Configuration_$memory, 1));

    // assume Implies(chain_status::$is_operating(), Ge(timestamp::spec_now_microseconds(), reconfiguration::$last_reconfiguration_time())) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:229:5+3042
    // global invariant at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/reconfiguration.spec.move:8:9+137
    assume ($1_chain_status_$is_operating($1_chain_status_GenesisEndMarker_$memory) ==> ($1_timestamp_spec_now_microseconds($1_timestamp_CurrentTimeMicroseconds_$memory) >= $1_reconfiguration_$last_reconfiguration_time($1_reconfiguration_Configuration_$memory)));

    // assume Implies(chain_status::$is_operating(), exists<block::BlockResource>(1)) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:229:5+3042
    // global invariant at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/block.spec.move:5:9+97
    assume ($1_chain_status_$is_operating($1_chain_status_GenesisEndMarker_$memory) ==> $ResourceExists($1_block_BlockResource_$memory, 1));

    // assume chain_status::$is_operating() at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.spec.move:137:9+38
    assume {:print "$at(3,5367,5405)"} true;
    assume $1_chain_status_$is_operating($1_chain_status_GenesisEndMarker_$memory);

    // trace_local[proposer]($t0) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:229:5+1
    assume {:print "$at(2,9812,9813)"} true;
    assume {:print "$track_local(44,4,0):", $t0} $t0 == $t0;

    // trace_local[stake_pool]($t1) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:229:5+1
    assume {:print "$track_local(44,4,1):", $t1} $t1 == $t1;

    // trace_local[execution_hash]($t2) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:229:5+1
    assume {:print "$track_local(44,4,2):", $t2} $t2 == $t2;

    // trace_local[metadata_location]($t3) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:229:5+1
    assume {:print "$track_local(44,4,3):", $t3} $t3 == $t3;

    // trace_local[metadata_hash]($t4) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:229:5+1
    assume {:print "$track_local(44,4,4):", $t4} $t4 == $t4;

    // trace_local[is_multi_step_proposal]($t5) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:229:5+1
    assume {:print "$track_local(44,4,5):", $t5} $t5 == $t5;

    // $t19 := signer::address_of($t0) on_abort goto L12 with $t20 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:237:32+28
    assume {:print "$at(2,10136,10164)"} true;
    call $t19 := $1_signer_address_of($t0);
    if ($abort_flag) {
        assume {:print "$at(2,10136,10164)"} true;
        $t20 := $abort_code;
        assume {:print "$track_abort(44,4):", $t20} $t20 == $t20;
        goto L12;
    }

    // trace_local[proposer_address]($t19) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:237:13+16
    assume {:print "$track_local(44,4,17):", $t19} $t19 == $t19;

    // $t21 := stake::get_delegated_voter($t1) on_abort goto L12 with $t20 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:238:17+38
    assume {:print "$at(2,10182,10220)"} true;
    call $t21 := $1_stake_get_delegated_voter($t1);
    if ($abort_flag) {
        assume {:print "$at(2,10182,10220)"} true;
        $t20 := $abort_code;
        assume {:print "$track_abort(44,4):", $t20} $t20 == $t20;
        goto L12;
    }

    // $t22 := ==($t21, $t19) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:238:56+2
    $t22 := $IsEqual'address'($t21, $t19);

    // if ($t22) goto L1 else goto L0 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:238:9+114
    if ($t22) { goto L1; } else { goto L0; }

    // label L1 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:238:9+114
L1:

    // goto L2 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:238:9+114
    assume {:print "$at(2,10174,10288)"} true;
    goto L2;

    // label L0 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:238:101+20
L0:

    // $t23 := 2 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:238:101+20
    assume {:print "$at(2,10266,10286)"} true;
    $t23 := 2;
    assume $IsValid'u64'($t23);

    // $t24 := error::invalid_argument($t23) on_abort goto L12 with $t20 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:238:77+45
    call $t24 := $1_error_invalid_argument($t23);
    if ($abort_flag) {
        assume {:print "$at(2,10242,10287)"} true;
        $t20 := $abort_code;
        assume {:print "$track_abort(44,4):", $t20} $t20 == $t20;
        goto L12;
    }

    // trace_abort($t24) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:238:9+114
    assume {:print "$at(2,10174,10288)"} true;
    assume {:print "$track_abort(44,4):", $t24} $t24 == $t24;

    // $t20 := move($t24) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:238:9+114
    $t20 := $t24;

    // goto L12 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:238:9+114
    goto L12;

    // label L2 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:241:65+16
    assume {:print "$at(2,10434,10450)"} true;
L2:

    // $t25 := 0x1 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:241:65+16
    assume {:print "$at(2,10434,10450)"} true;
    $t25 := 1;
    assume $IsValid'address'($t25);

    // $t26 := get_global<aptos_governance::GovernanceConfig>($t25) on_abort goto L12 with $t20 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:241:33+13
    if (!$ResourceExists($1_aptos_governance_GovernanceConfig_$memory, $t25)) {
        call $ExecFailureAbort();
    } else {
        $t26 := $ResourceValue($1_aptos_governance_GovernanceConfig_$memory, $t25);
    }
    if ($abort_flag) {
        assume {:print "$at(2,10402,10415)"} true;
        $t20 := $abort_code;
        assume {:print "$track_abort(44,4):", $t20} $t20 == $t20;
        goto L12;
    }

    // trace_local[governance_config]($t26) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:241:13+17
    assume {:print "$track_local(44,4,13):", $t26} $t26 == $t26;

    // assume Identical($t27, global<staking_config::StakingConfig>(1)) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.spec.move:617:9+77
    assume {:print "$at(3,37678,37755)"} true;
    assume ($t27 == $ResourceValue($1_staking_config_StakingConfig_$memory, 1));

    // assume Identical($t28, select staking_config::StakingConfig.allow_validator_set_change($t27)) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.spec.move:619:9+75
    assume {:print "$at(3,37840,37915)"} true;
    assume ($t28 == $allow_validator_set_change#$1_staking_config_StakingConfig($t27));

    // assume Identical($t29, global<stake::StakePool>($t1)) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.spec.move:620:9+56
    assume {:print "$at(3,37924,37980)"} true;
    assume ($t29 == $ResourceValue($1_stake_StakePool_$memory, $t1));

    // $t30 := aptos_governance::get_voting_power($t1) on_abort goto L12 with $t20 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:242:29+28
    assume {:print "$at(2,10481,10509)"} true;
    call $t30 := $1_aptos_governance_get_voting_power($t1);
    if ($abort_flag) {
        assume {:print "$at(2,10481,10509)"} true;
        $t20 := $abort_code;
        assume {:print "$track_abort(44,4):", $t20} $t20 == $t20;
        goto L12;
    }

    // $t31 := get_field<aptos_governance::GovernanceConfig>.required_proposer_stake($t26) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:244:30+41
    assume {:print "$at(2,10557,10598)"} true;
    $t31 := $required_proposer_stake#$1_aptos_governance_GovernanceConfig($t26);

    // $t32 := >=($t30, $t31) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:244:27+2
    call $t32 := $Ge($t30, $t31);

    // if ($t32) goto L4 else goto L3 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:243:9+157
    assume {:print "$at(2,10519,10676)"} true;
    if ($t32) { goto L4; } else { goto L3; }

    // label L4 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:243:9+157
L4:

    // goto L5 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:243:9+157
    assume {:print "$at(2,10519,10676)"} true;
    goto L5;

    // label L3 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:243:9+157
L3:

    // $t33 := 1 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:245:37+28
    assume {:print "$at(2,10636,10664)"} true;
    $t33 := 1;
    assume $IsValid'u64'($t33);

    // $t34 := error::invalid_argument($t33) on_abort goto L12 with $t20 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:245:13+53
    call $t34 := $1_error_invalid_argument($t33);
    if ($abort_flag) {
        assume {:print "$at(2,10612,10665)"} true;
        $t20 := $abort_code;
        assume {:print "$track_abort(44,4):", $t20} $t20 == $t20;
        goto L12;
    }

    // trace_abort($t34) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:243:9+157
    assume {:print "$at(2,10519,10676)"} true;
    assume {:print "$track_abort(44,4):", $t34} $t34 == $t34;

    // $t20 := move($t34) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:243:9+157
    $t20 := $t34;

    // goto L12 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:243:9+157
    goto L12;

    // label L5 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:249:28+24
    assume {:print "$at(2,10810,10834)"} true;
L5:

    // $t35 := timestamp::now_seconds() on_abort goto L12 with $t20 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:249:28+24
    assume {:print "$at(2,10810,10834)"} true;
    call $t35 := $1_timestamp_now_seconds();
    if ($abort_flag) {
        assume {:print "$at(2,10810,10834)"} true;
        $t20 := $abort_code;
        assume {:print "$track_abort(44,4):", $t20} $t20 == $t20;
        goto L12;
    }

    // $t36 := get_field<aptos_governance::GovernanceConfig>.voting_duration_secs($t26) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:250:50+38
    assume {:print "$at(2,10885,10923)"} true;
    $t36 := $voting_duration_secs#$1_aptos_governance_GovernanceConfig($t26);

    // $t37 := +($t35, $t36) on_abort goto L12 with $t20 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:250:48+1
    call $t37 := $AddU64($t35, $t36);
    if ($abort_flag) {
        assume {:print "$at(2,10883,10884)"} true;
        $t20 := $abort_code;
        assume {:print "$track_abort(44,4):", $t20} $t20 == $t20;
        goto L12;
    }

    // trace_local[proposal_expiration]($t37) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:250:13+19
    assume {:print "$track_local(44,4,14):", $t37} $t37 == $t37;

    // $t38 := stake::get_lockup_secs($t1) on_abort goto L12 with $t20 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:252:13+34
    assume {:print "$at(2,10954,10988)"} true;
    call $t38 := $1_stake_get_lockup_secs($t1);
    if ($abort_flag) {
        assume {:print "$at(2,10954,10988)"} true;
        $t20 := $abort_code;
        assume {:print "$track_abort(44,4):", $t20} $t20 == $t20;
        goto L12;
    }

    // $t39 := >=($t38, $t37) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:252:48+2
    call $t39 := $Ge($t38, $t37);

    // if ($t39) goto L7 else goto L6 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:251:9+154
    assume {:print "$at(2,10933,11087)"} true;
    if ($t39) { goto L7; } else { goto L6; }

    // label L7 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:251:9+154
L7:

    // goto L8 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:251:9+154
    assume {:print "$at(2,10933,11087)"} true;
    goto L8;

    // label L6 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:251:9+154
L6:

    // $t40 := 3 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:253:37+26
    assume {:print "$at(2,11049,11075)"} true;
    $t40 := 3;
    assume $IsValid'u64'($t40);

    // $t41 := error::invalid_argument($t40) on_abort goto L12 with $t20 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:253:13+51
    call $t41 := $1_error_invalid_argument($t40);
    if ($abort_flag) {
        assume {:print "$at(2,11025,11076)"} true;
        $t20 := $abort_code;
        assume {:print "$track_abort(44,4):", $t20} $t20 == $t20;
        goto L12;
    }

    // trace_abort($t41) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:251:9+154
    assume {:print "$at(2,10933,11087)"} true;
    assume {:print "$track_abort(44,4):", $t41} $t41 == $t41;

    // $t20 := move($t41) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:251:9+154
    $t20 := $t41;

    // goto L12 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:251:9+154
    goto L12;

    // label L8 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:257:58+17
    assume {:print "$at(2,11197,11214)"} true;
L8:

    // $t42 := aptos_governance::create_proposal_metadata($t3, $t4) on_abort goto L12 with $t20 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:257:33+58
    assume {:print "$at(2,11172,11230)"} true;
    call $t42 := $1_aptos_governance_create_proposal_metadata($t3, $t4);
    if ($abort_flag) {
        assume {:print "$at(2,11172,11230)"} true;
        $t20 := $abort_code;
        assume {:print "$track_abort(44,4):", $t20} $t20 == $t20;
        goto L12;
    }

    // trace_local[proposal_metadata]($t42) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:257:13+17
    assume {:print "$track_local(44,4,16):", $t42} $t42 == $t42;

    // assume Identical($t43, select type_info::TypeInfo.account_address(type_info::$type_of<aptos_coin::AptosCoin>())) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.spec.move:91:9+63
    assume {:print "$at(93,3461,3524)"} true;
    assume ($t43 == $account_address#$1_type_info_TypeInfo($1_type_info_TypeInfo(1, Vec(DefaultVecMap()[0 := 97][1 := 112][2 := 116][3 := 111][4 := 115][5 := 95][6 := 99][7 := 111][8 := 105][9 := 110], 10), Vec(DefaultVecMap()[0 := 65][1 := 112][2 := 116][3 := 111][4 := 115][5 := 67][6 := 111][7 := 105][8 := 110], 9))));

    // assume Identical($t44, select coin::CoinInfo.supply(global<coin::CoinInfo<aptos_coin::AptosCoin>>($t43))) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.spec.move:93:9+64
    assume {:print "$at(93,3591,3655)"} true;
    assume ($t44 == $supply#$1_coin_CoinInfo'$1_aptos_coin_AptosCoin'($ResourceValue($1_coin_CoinInfo'$1_aptos_coin_AptosCoin'_$memory, $t43)));

    // assume Identical($t45, option::spec_borrow<optional_aggregator::OptionalAggregator>($t44)) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.spec.move:94:9+47
    assume {:print "$at(93,3664,3711)"} true;
    assume ($t45 == $1_option_spec_borrow'$1_optional_aggregator_OptionalAggregator'($t44));

    // assume Identical($t46, optional_aggregator::optional_aggregator_value($t45)) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.spec.move:95:9+67
    assume {:print "$at(93,3720,3787)"} true;
    assume ($t46 == $1_optional_aggregator_optional_aggregator_value($t45));

    // $t47 := coin::supply<aptos_coin::AptosCoin>() on_abort goto L12 with $t20 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:263:41+25
    assume {:print "$at(2,11673,11698)"} true;
    call $t47 := $1_coin_supply'$1_aptos_coin_AptosCoin'();
    if ($abort_flag) {
        assume {:print "$at(2,11673,11698)"} true;
        $t20 := $abort_code;
        assume {:print "$track_abort(44,4):", $t20} $t20 == $t20;
        goto L12;
    }

    // trace_local[total_voting_token_supply]($t47) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:263:13+25
    assume {:print "$track_local(44,4,18):", $t47} $t47 == $t47;

    // $t48 := opaque begin: option::none<u128>() at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:264:47+20
    assume {:print "$at(2,11746,11766)"} true;

    // assume And(WellFormed($t48), Le(Len<u128>(select option::Option.vec($t48)), 1)) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:264:47+20
    assume ($IsValid'$1_option_Option'u128''($t48) && (LenVec($vec#$1_option_Option'u128'($t48)) <= 1));

    // assume Eq<option::Option<u128>>($t48, option::spec_none<u128>()) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:264:47+20
    assume $IsEqual'$1_option_Option'u128''($t48, $1_option_spec_none'u128'());

    // $t48 := opaque end: option::none<u128>() at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:264:47+20

    // $t12 := $t48 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:264:13+31
    $t12 := $t48;

    // trace_local[early_resolution_vote_threshold]($t48) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:264:13+31
    assume {:print "$track_local(44,4,12):", $t48} $t48 == $t48;

    // $t49 := opaque begin: option::is_some<u128>($t47) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:265:13+43
    assume {:print "$at(2,11780,11823)"} true;

    // assume WellFormed($t49) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:265:13+43
    assume $IsValid'bool'($t49);

    // assume Eq<bool>($t49, option::spec_is_some<u128>($t47)) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:265:13+43
    assume $IsEqual'bool'($t49, $1_option_spec_is_some'u128'($t47));

    // $t49 := opaque end: option::is_some<u128>($t47) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:265:13+43

    // if ($t49) goto L10 else goto L9 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:265:9+267
    if ($t49) { goto L10; } else { goto L9; }

    // label L10 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:266:48+26
    assume {:print "$at(2,11874,11900)"} true;
L10:

    // $t50 := opaque begin: option::borrow<u128>($t47) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:266:33+42
    assume {:print "$at(2,11859,11901)"} true;

    // assume Identical($t51, option::spec_is_none<u128>($t47)) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:266:33+42
    assume ($t51 == $1_option_spec_is_none'u128'($t47));

    // if ($t51) goto L14 else goto L13 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:266:33+42
    if ($t51) { goto L14; } else { goto L13; }

    // label L14 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:266:33+42
L14:

    // assume And(option::spec_is_none<u128>($t47), Eq(262145, $t20)) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:266:33+42
    assume {:print "$at(2,11859,11901)"} true;
    assume ($1_option_spec_is_none'u128'($t47) && $IsEqual'num'(262145, $t20));

    // trace_abort($t20) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:266:33+42
    assume {:print "$at(2,11859,11901)"} true;
    assume {:print "$track_abort(44,4):", $t20} $t20 == $t20;

    // goto L12 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:266:33+42
    goto L12;

    // label L13 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:266:33+42
L13:

    // assume WellFormed($t50) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:266:33+42
    assume {:print "$at(2,11859,11901)"} true;
    assume $IsValid'u128'($t50);

    // assume Eq<u128>($t50, option::spec_borrow<u128>($t47)) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:266:33+42
    assume $IsEqual'u128'($t50, $1_option_spec_borrow'u128'($t47));

    // $t50 := opaque end: option::borrow<u128>($t47) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:266:33+42

    // $t52 := 2 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:268:75+1
    assume {:print "$at(2,12026,12027)"} true;
    $t52 := 2;
    assume $IsValid'u128'($t52);

    // $t53 := /($t50, $t52) on_abort goto L12 with $t20 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:268:73+1
    call $t53 := $Div($t50, $t52);
    if ($abort_flag) {
        assume {:print "$at(2,12024,12025)"} true;
        $t20 := $abort_code;
        assume {:print "$track_abort(44,4):", $t20} $t20 == $t20;
        goto L12;
    }

    // $t54 := 1 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:268:79+1
    $t54 := 1;
    assume $IsValid'u128'($t54);

    // $t55 := +($t53, $t54) on_abort goto L12 with $t20 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:268:77+1
    call $t55 := $AddU128($t53, $t54);
    if ($abort_flag) {
        assume {:print "$at(2,12028,12029)"} true;
        $t20 := $abort_code;
        assume {:print "$track_abort(44,4):", $t20} $t20 == $t20;
        goto L12;
    }

    // $t56 := opaque begin: option::some<u128>($t55) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:268:47+34

    // assume And(WellFormed($t56), Le(Len<u128>(select option::Option.vec($t56)), 1)) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:268:47+34
    assume ($IsValid'$1_option_Option'u128''($t56) && (LenVec($vec#$1_option_Option'u128'($t56)) <= 1));

    // assume Eq<option::Option<u128>>($t56, option::spec_some<u128>($t55)) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:268:47+34
    assume $IsEqual'$1_option_Option'u128''($t56, $1_option_spec_some'u128'($t55));

    // $t56 := opaque end: option::some<u128>($t55) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:268:47+34

    // $t12 := $t56 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:268:13+31
    $t12 := $t56;

    // trace_local[early_resolution_vote_threshold]($t56) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:268:13+31
    assume {:print "$track_local(44,4,12):", $t56} $t56 == $t56;

    // label L9 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:272:13+16
    assume {:print "$at(2,12112,12128)"} true;
L9:

    // $t57 := 0x1 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:273:13+16
    assume {:print "$at(2,12142,12158)"} true;
    $t57 := 1;
    assume $IsValid'address'($t57);

    // $t58 := governance_proposal::create_proposal() on_abort goto L12 with $t20 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:274:13+38
    assume {:print "$at(2,12172,12210)"} true;
    call $t58 := $1_governance_proposal_create_proposal();
    if ($abort_flag) {
        assume {:print "$at(2,12172,12210)"} true;
        $t20 := $abort_code;
        assume {:print "$track_abort(44,4):", $t20} $t20 == $t20;
        goto L12;
    }

    // $t59 := get_field<aptos_governance::GovernanceConfig>.min_voting_threshold($t26) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:276:13+38
    assume {:print "$at(2,12252,12290)"} true;
    $t59 := $min_voting_threshold#$1_aptos_governance_GovernanceConfig($t26);

    // assume Identical($t60, global<voting::VotingForum<governance_proposal::GovernanceProposal>>($t57)) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.spec.move:69:9+75
    assume {:print "$at(154,2710,2785)"} true;
    assume ($t60 == $ResourceValue($1_voting_VotingForum'$1_governance_proposal_GovernanceProposal'_$memory, $t57));

    // assume Identical($t61, select voting::VotingForum.next_proposal_id($t60)) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.spec.move:70:9+48
    assume {:print "$at(154,2794,2842)"} true;
    assume ($t61 == $next_proposal_id#$1_voting_VotingForum'$1_governance_proposal_GovernanceProposal'($t60));

    // assume Identical($t62, string::spec_utf8([73, 83, 95, 77, 85, 76, 84, 73, 95, 83, 84, 69, 80, 95, 80, 82, 79, 80, 79, 83, 65, 76, 95, 75, 69, 89])) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.spec.move:78:9+71
    assume {:print "$at(154,3361,3432)"} true;
    assume ($t62 == $1_string_spec_utf8(ConcatVec(ConcatVec(ConcatVec(ConcatVec(ConcatVec(ConcatVec(MakeVec4(73, 83, 95, 77), MakeVec4(85, 76, 84, 73)), MakeVec4(95, 83, 84, 69)), MakeVec4(80, 95, 80, 82)), MakeVec4(79, 80, 79, 83)), MakeVec4(65, 76, 95, 75)), MakeVec2(69, 89))));

    // assume Identical($t63, string::spec_utf8([73, 83, 95, 77, 85, 76, 84, 73, 95, 83, 84, 69, 80, 95, 80, 82, 79, 80, 79, 83, 65, 76, 95, 73, 78, 95, 69, 88, 69, 67, 85, 84, 73, 79, 78])) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.spec.move:81:9+101
    assume {:print "$at(154,3577,3678)"} true;
    assume ($t63 == $1_string_spec_utf8(ConcatVec(ConcatVec(ConcatVec(ConcatVec(ConcatVec(ConcatVec(ConcatVec(ConcatVec(MakeVec4(73, 83, 95, 77), MakeVec4(85, 76, 84, 73)), MakeVec4(95, 83, 84, 69)), MakeVec4(80, 95, 80, 82)), MakeVec4(79, 80, 79, 83)), MakeVec4(65, 76, 95, 73)), MakeVec4(78, 95, 69, 88)), MakeVec4(69, 67, 85, 84)), MakeVec3(73, 79, 78))));

    // assert chain_status::$is_operating() at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/voting.spec.move:57:9+38
    assume {:print "$at(154,2295,2333)"} true;
    assert {:msg "assert_failed(154,2295,2333): precondition does not hold at this call"}
      $1_chain_status_$is_operating($1_chain_status_GenesisEndMarker_$memory);

    // $t64 := voting::create_proposal_v2<governance_proposal::GovernanceProposal>($t19, $t57, $t58, $t2, $t59, $t37, $t12, $t42, $t5) on_abort goto L12 with $t20 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:271:27+374
    assume {:print "$at(2,12072,12446)"} true;
    call $t64 := $1_voting_create_proposal_v2'$1_governance_proposal_GovernanceProposal'($t19, $t57, $t58, $t2, $t59, $t37, $t12, $t42, $t5);
    if ($abort_flag) {
        assume {:print "$at(2,12072,12446)"} true;
        $t20 := $abort_code;
        assume {:print "$track_abort(44,4):", $t20} $t20 == $t20;
        goto L12;
    }

    // trace_local[proposal_id]($t64) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:271:13+11
    assume {:print "$track_local(44,4,15):", $t64} $t64 == $t64;

    // $t65 := 0x1 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:283:58+16
    assume {:print "$at(2,12506,12522)"} true;
    $t65 := 1;
    assume $IsValid'address'($t65);

    // $t66 := borrow_global<aptos_governance::GovernanceEvents>($t65) on_abort goto L12 with $t20 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:283:22+17
    if (!$ResourceExists($1_aptos_governance_GovernanceEvents_$memory, $t65)) {
        call $ExecFailureAbort();
    } else {
        $t66 := $Mutation($Global($t65), EmptyVec(), $ResourceValue($1_aptos_governance_GovernanceEvents_$memory, $t65));
    }
    if ($abort_flag) {
        assume {:print "$at(2,12470,12487)"} true;
        $t20 := $abort_code;
        assume {:print "$track_abort(44,4):", $t20} $t20 == $t20;
        goto L12;
    }

    // $t67 := borrow_field<aptos_governance::GovernanceEvents>.create_proposal_events($t66) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:285:13+34
    assume {:print "$at(2,12585,12619)"} true;
    $t67 := $ChildMutation($t66, 0, $create_proposal_events#$1_aptos_governance_GovernanceEvents($Dereference($t66)));

    // $t68 := pack aptos_governance::CreateProposalEvent($t19, $t1, $t64, $t2, $t42) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:286:13+203
    assume {:print "$at(2,12633,12836)"} true;
    $t68 := $1_aptos_governance_CreateProposalEvent($t19, $t1, $t64, $t2, $t42);

    // opaque begin: event::emit_event<aptos_governance::CreateProposalEvent>($t67, $t68) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:284:9+314
    assume {:print "$at(2,12533,12847)"} true;

    // opaque end: event::emit_event<aptos_governance::CreateProposalEvent>($t67, $t68) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:284:9+314

    // write_back[Reference($t66).create_proposal_events (event::EventHandle<aptos_governance::CreateProposalEvent>)]($t67) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:284:9+314
    $t66 := $UpdateMutation($t66, $Update'$1_aptos_governance_GovernanceEvents'_create_proposal_events($Dereference($t66), $Dereference($t67)));

    // write_back[aptos_governance::GovernanceEvents@]($t66) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:284:9+314
    $1_aptos_governance_GovernanceEvents_$memory := $ResourceUpdate($1_aptos_governance_GovernanceEvents_$memory, $GlobalLocationAddress($t66),
        $Dereference($t66));

    // label L11 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:294:5+1
    assume {:print "$at(2,12853,12854)"} true;
L11:

    // assert Not(true) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.spec.move:136:9+15
    assume {:print "$at(3,5343,5358)"} true;
    assert {:msg "assert_failed(3,5343,5358): function does not abort under this condition"}
      !true;

    // assert Not(true) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.spec.move:138:9+15
    assume {:print "$at(3,5414,5429)"} true;
    assert {:msg "assert_failed(3,5414,5429): function does not abort under this condition"}
      !true;

    // return () at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.spec.move:138:9+15
    return;

    // label L12 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:294:5+1
    assume {:print "$at(2,12853,12854)"} true;
L12:

    // assert Or(true, true) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.spec.move:121:5+6102
    assume {:print "$at(3,4654,10756)"} true;
    assert {:msg "assert_failed(3,4654,10756): abort not covered by any of the `aborts_if` clauses"}
      (true || true);

    // abort($t20) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.spec.move:121:5+6102
    $abort_code := $t20;
    $abort_flag := true;
    return;

}

// fun aptos_governance::create_proposal_metadata [baseline] at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:453:5+608
procedure {:inline 1} $1_aptos_governance_create_proposal_metadata(_$t0: Vec (int), _$t1: Vec (int)) returns ($ret0: Table int (Vec (int)))
{
    // declare local variables
    var $t2: $1_string_String;
    var $t3: $1_string_String;
    var $t4: Table int (Vec (int));
    var $t5: $1_string_String;
    var $t6: int;
    var $t7: int;
    var $t8: int;
    var $t9: bool;
    var $t10: int;
    var $t11: int;
    var $t12: $1_string_String;
    var $t13: int;
    var $t14: int;
    var $t15: bool;
    var $t16: int;
    var $t17: int;
    var $t18: $Mutation (Table int (Vec (int)));
    var $t19: Vec (int);
    var $t20: $1_string_String;
    var $t21: $Mutation (Table int (Vec (int)));
    var $t22: Vec (int);
    var $t23: $1_string_String;
    var $t24: Table int (Vec (int));
    var $t0: Vec (int);
    var $t1: Vec (int);
    var $temp_0'$1_simple_map_SimpleMap'$1_string_String_vec'u8''': Table int (Vec (int));
    var $temp_0'vec'u8'': Vec (int);
    $t0 := _$t0;
    $t1 := _$t1;

    // bytecode translation starts here
    // trace_local[metadata_location]($t0) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:453:5+1
    assume {:print "$at(2,20897,20898)"} true;
    assume {:print "$track_local(44,3,0):", $t0} $t0 == $t0;

    // trace_local[metadata_hash]($t1) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:453:5+1
    assume {:print "$track_local(44,3,1):", $t1} $t1 == $t1;

    // $t5 := string::utf8($t0) on_abort goto L7 with $t6 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:454:33+23
    assume {:print "$at(2,21049,21072)"} true;
    call $t5 := $1_string_utf8($t0);
    if ($abort_flag) {
        assume {:print "$at(2,21049,21072)"} true;
        $t6 := $abort_code;
        assume {:print "$track_abort(44,3):", $t6} $t6 == $t6;
        goto L7;
    }

    // $t7 := string::length($t5) on_abort goto L7 with $t6 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:454:17+40
    call $t7 := $1_string_length($t5);
    if ($abort_flag) {
        assume {:print "$at(2,21033,21073)"} true;
        $t6 := $abort_code;
        assume {:print "$track_abort(44,3):", $t6} $t6 == $t6;
        goto L7;
    }

    // $t8 := 256 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:454:61+3
    $t8 := 256;
    assume $IsValid'u64'($t8);

    // $t9 := <=($t7, $t8) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:454:58+2
    call $t9 := $Le($t7, $t8);

    // if ($t9) goto L1 else goto L0 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:454:9+110
    if ($t9) { goto L1; } else { goto L0; }

    // label L1 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:454:9+110
L1:

    // goto L2 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:454:9+110
    assume {:print "$at(2,21025,21135)"} true;
    goto L2;

    // label L0 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:454:90+27
L0:

    // $t10 := 9 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:454:90+27
    assume {:print "$at(2,21106,21133)"} true;
    $t10 := 9;
    assume $IsValid'u64'($t10);

    // $t11 := error::invalid_argument($t10) on_abort goto L7 with $t6 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:454:66+52
    call $t11 := $1_error_invalid_argument($t10);
    if ($abort_flag) {
        assume {:print "$at(2,21082,21134)"} true;
        $t6 := $abort_code;
        assume {:print "$track_abort(44,3):", $t6} $t6 == $t6;
        goto L7;
    }

    // trace_abort($t11) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:454:9+110
    assume {:print "$at(2,21025,21135)"} true;
    assume {:print "$track_abort(44,3):", $t11} $t11 == $t11;

    // $t6 := move($t11) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:454:9+110
    $t6 := $t11;

    // goto L7 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:454:9+110
    goto L7;

    // label L2 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:455:38+13
    assume {:print "$at(2,21174,21187)"} true;
L2:

    // $t12 := string::utf8($t1) on_abort goto L7 with $t6 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:455:33+19
    assume {:print "$at(2,21169,21188)"} true;
    call $t12 := $1_string_utf8($t1);
    if ($abort_flag) {
        assume {:print "$at(2,21169,21188)"} true;
        $t6 := $abort_code;
        assume {:print "$track_abort(44,3):", $t6} $t6 == $t6;
        goto L7;
    }

    // $t13 := string::length($t12) on_abort goto L7 with $t6 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:455:17+36
    call $t13 := $1_string_length($t12);
    if ($abort_flag) {
        assume {:print "$at(2,21153,21189)"} true;
        $t6 := $abort_code;
        assume {:print "$track_abort(44,3):", $t6} $t6 == $t6;
        goto L7;
    }

    // $t14 := 256 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:455:57+3
    $t14 := 256;
    assume $IsValid'u64'($t14);

    // $t15 := <=($t13, $t14) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:455:54+2
    call $t15 := $Le($t13, $t14);

    // if ($t15) goto L4 else goto L3 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:455:9+102
    if ($t15) { goto L4; } else { goto L3; }

    // label L4 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:455:9+102
L4:

    // goto L5 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:455:9+102
    assume {:print "$at(2,21145,21247)"} true;
    goto L5;

    // label L3 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:455:86+23
L3:

    // $t16 := 10 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:455:86+23
    assume {:print "$at(2,21222,21245)"} true;
    $t16 := 10;
    assume $IsValid'u64'($t16);

    // $t17 := error::invalid_argument($t16) on_abort goto L7 with $t6 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:455:62+48
    call $t17 := $1_error_invalid_argument($t16);
    if ($abort_flag) {
        assume {:print "$at(2,21198,21246)"} true;
        $t6 := $abort_code;
        assume {:print "$track_abort(44,3):", $t6} $t6 == $t6;
        goto L7;
    }

    // trace_abort($t17) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:455:9+102
    assume {:print "$at(2,21145,21247)"} true;
    assume {:print "$track_abort(44,3):", $t17} $t17 == $t17;

    // $t6 := move($t17) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:455:9+102
    $t6 := $t17;

    // goto L7 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:455:9+102
    goto L7;

    // label L5 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:457:24+40
    assume {:print "$at(2,21273,21313)"} true;
L5:

    // $t4 := simple_map::create<string::String, vector<u8>>() on_abort goto L7 with $t6 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:457:24+40
    assume {:print "$at(2,21273,21313)"} true;
    call $t4 := $1_simple_map_create'$1_string_String_vec'u8''();
    if ($abort_flag) {
        assume {:print "$at(2,21273,21313)"} true;
        $t6 := $abort_code;
        assume {:print "$track_abort(44,3):", $t6} $t6 == $t6;
        goto L7;
    }

    // trace_local[metadata]($t4) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:457:13+8
    assume {:print "$track_local(44,3,4):", $t4} $t4 == $t4;

    // $t18 := borrow_local($t4) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:458:25+13
    assume {:print "$at(2,21339,21352)"} true;
    $t18 := $Mutation($Local(4), EmptyVec(), $t4);

    // $t19 := [109, 101, 116, 97, 100, 97, 116, 97, 95, 108, 111, 99, 97, 116, 105, 111, 110] at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:458:45+21
    $t19 := ConcatVec(ConcatVec(ConcatVec(ConcatVec(MakeVec4(109, 101, 116, 97), MakeVec4(100, 97, 116, 97)), MakeVec4(95, 108, 111, 99)), MakeVec4(97, 116, 105, 111)), MakeVec1(110));
    assume $IsValid'vec'u8''($t19);

    // $t20 := string::utf8($t19) on_abort goto L7 with $t6 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:458:40+27
    call $t20 := $1_string_utf8($t19);
    if ($abort_flag) {
        assume {:print "$at(2,21354,21381)"} true;
        $t6 := $abort_code;
        assume {:print "$track_abort(44,3):", $t6} $t6 == $t6;
        goto L7;
    }

    // simple_map::add<string::String, vector<u8>>($t18, $t20, $t0) on_abort goto L7 with $t6 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:458:9+78
    call $t18 := $1_simple_map_add'$1_string_String_vec'u8''($t18, $t20, $t0);
    if ($abort_flag) {
        assume {:print "$at(2,21323,21401)"} true;
        $t6 := $abort_code;
        assume {:print "$track_abort(44,3):", $t6} $t6 == $t6;
        goto L7;
    }

    // write_back[LocalRoot($t4)@]($t18) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:458:9+78
    $t4 := $Dereference($t18);

    // trace_local[metadata]($t4) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:458:9+78
    assume {:print "$track_local(44,3,4):", $t4} $t4 == $t4;

    // $t21 := borrow_local($t4) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:459:25+13
    assume {:print "$at(2,21427,21440)"} true;
    $t21 := $Mutation($Local(4), EmptyVec(), $t4);

    // $t22 := [109, 101, 116, 97, 100, 97, 116, 97, 95, 104, 97, 115, 104] at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:459:45+17
    $t22 := ConcatVec(ConcatVec(ConcatVec(MakeVec4(109, 101, 116, 97), MakeVec4(100, 97, 116, 97)), MakeVec4(95, 104, 97, 115)), MakeVec1(104));
    assume $IsValid'vec'u8''($t22);

    // $t23 := string::utf8($t22) on_abort goto L7 with $t6 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:459:40+23
    call $t23 := $1_string_utf8($t22);
    if ($abort_flag) {
        assume {:print "$at(2,21442,21465)"} true;
        $t6 := $abort_code;
        assume {:print "$track_abort(44,3):", $t6} $t6 == $t6;
        goto L7;
    }

    // simple_map::add<string::String, vector<u8>>($t21, $t23, $t1) on_abort goto L7 with $t6 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:459:9+70
    call $t21 := $1_simple_map_add'$1_string_String_vec'u8''($t21, $t23, $t1);
    if ($abort_flag) {
        assume {:print "$at(2,21411,21481)"} true;
        $t6 := $abort_code;
        assume {:print "$track_abort(44,3):", $t6} $t6 == $t6;
        goto L7;
    }

    // write_back[LocalRoot($t4)@]($t21) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:459:9+70
    $t4 := $Dereference($t21);

    // trace_local[metadata]($t4) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:459:9+70
    assume {:print "$track_local(44,3,4):", $t4} $t4 == $t4;

    // $t24 := move($t4) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:460:9+8
    assume {:print "$at(2,21491,21499)"} true;
    $t24 := $t4;

    // trace_return[0]($t24) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:460:9+8
    assume {:print "$track_return(44,3,0):", $t24} $t24 == $t24;

    // label L6 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:461:5+1
    assume {:print "$at(2,21504,21505)"} true;
L6:

    // return $t24 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:461:5+1
    assume {:print "$at(2,21504,21505)"} true;
    $ret0 := $t24;
    return;

    // label L7 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:461:5+1
L7:

    // abort($t6) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:461:5+1
    assume {:print "$at(2,21504,21505)"} true;
    $abort_code := $t6;
    $abort_flag := true;
    return;

}

// fun aptos_governance::create_proposal_metadata [verification] at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:453:5+608
procedure {:timeLimit 40} $1_aptos_governance_create_proposal_metadata$verify(_$t0: Vec (int), _$t1: Vec (int)) returns ($ret0: Table int (Vec (int)))
{
    // declare local variables
    var $t2: $1_string_String;
    var $t3: $1_string_String;
    var $t4: Table int (Vec (int));
    var $t5: $1_string_String;
    var $t6: int;
    var $t7: int;
    var $t8: int;
    var $t9: bool;
    var $t10: int;
    var $t11: int;
    var $t12: $1_string_String;
    var $t13: int;
    var $t14: int;
    var $t15: bool;
    var $t16: int;
    var $t17: int;
    var $t18: $Mutation (Table int (Vec (int)));
    var $t19: Vec (int);
    var $t20: $1_string_String;
    var $t21: $Mutation (Table int (Vec (int)));
    var $t22: Vec (int);
    var $t23: $1_string_String;
    var $t24: Table int (Vec (int));
    var $t0: Vec (int);
    var $t1: Vec (int);
    var $temp_0'$1_simple_map_SimpleMap'$1_string_String_vec'u8''': Table int (Vec (int));
    var $temp_0'vec'u8'': Vec (int);
    $t0 := _$t0;
    $t1 := _$t1;

    // verification entrypoint assumptions
    call $InitVerification();

    // bytecode translation starts here
    // assume WellFormed($t0) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:453:5+1
    assume {:print "$at(2,20897,20898)"} true;
    assume $IsValid'vec'u8''($t0);

    // assume WellFormed($t1) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:453:5+1
    assume $IsValid'vec'u8''($t1);

    // trace_local[metadata_location]($t0) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:453:5+1
    assume {:print "$track_local(44,3,0):", $t0} $t0 == $t0;

    // trace_local[metadata_hash]($t1) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:453:5+1
    assume {:print "$track_local(44,3,1):", $t1} $t1 == $t1;

    // $t5 := string::utf8($t0) on_abort goto L7 with $t6 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:454:33+23
    assume {:print "$at(2,21049,21072)"} true;
    call $t5 := $1_string_utf8($t0);
    if ($abort_flag) {
        assume {:print "$at(2,21049,21072)"} true;
        $t6 := $abort_code;
        assume {:print "$track_abort(44,3):", $t6} $t6 == $t6;
        goto L7;
    }

    // $t7 := string::length($t5) on_abort goto L7 with $t6 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:454:17+40
    call $t7 := $1_string_length($t5);
    if ($abort_flag) {
        assume {:print "$at(2,21033,21073)"} true;
        $t6 := $abort_code;
        assume {:print "$track_abort(44,3):", $t6} $t6 == $t6;
        goto L7;
    }

    // $t8 := 256 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:454:61+3
    $t8 := 256;
    assume $IsValid'u64'($t8);

    // $t9 := <=($t7, $t8) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:454:58+2
    call $t9 := $Le($t7, $t8);

    // if ($t9) goto L1 else goto L0 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:454:9+110
    if ($t9) { goto L1; } else { goto L0; }

    // label L1 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:454:9+110
L1:

    // goto L2 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:454:9+110
    assume {:print "$at(2,21025,21135)"} true;
    goto L2;

    // label L0 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:454:90+27
L0:

    // $t10 := 9 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:454:90+27
    assume {:print "$at(2,21106,21133)"} true;
    $t10 := 9;
    assume $IsValid'u64'($t10);

    // $t11 := error::invalid_argument($t10) on_abort goto L7 with $t6 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:454:66+52
    call $t11 := $1_error_invalid_argument($t10);
    if ($abort_flag) {
        assume {:print "$at(2,21082,21134)"} true;
        $t6 := $abort_code;
        assume {:print "$track_abort(44,3):", $t6} $t6 == $t6;
        goto L7;
    }

    // trace_abort($t11) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:454:9+110
    assume {:print "$at(2,21025,21135)"} true;
    assume {:print "$track_abort(44,3):", $t11} $t11 == $t11;

    // $t6 := move($t11) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:454:9+110
    $t6 := $t11;

    // goto L7 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:454:9+110
    goto L7;

    // label L2 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:455:38+13
    assume {:print "$at(2,21174,21187)"} true;
L2:

    // $t12 := string::utf8($t1) on_abort goto L7 with $t6 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:455:33+19
    assume {:print "$at(2,21169,21188)"} true;
    call $t12 := $1_string_utf8($t1);
    if ($abort_flag) {
        assume {:print "$at(2,21169,21188)"} true;
        $t6 := $abort_code;
        assume {:print "$track_abort(44,3):", $t6} $t6 == $t6;
        goto L7;
    }

    // $t13 := string::length($t12) on_abort goto L7 with $t6 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:455:17+36
    call $t13 := $1_string_length($t12);
    if ($abort_flag) {
        assume {:print "$at(2,21153,21189)"} true;
        $t6 := $abort_code;
        assume {:print "$track_abort(44,3):", $t6} $t6 == $t6;
        goto L7;
    }

    // $t14 := 256 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:455:57+3
    $t14 := 256;
    assume $IsValid'u64'($t14);

    // $t15 := <=($t13, $t14) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:455:54+2
    call $t15 := $Le($t13, $t14);

    // if ($t15) goto L4 else goto L3 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:455:9+102
    if ($t15) { goto L4; } else { goto L3; }

    // label L4 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:455:9+102
L4:

    // goto L5 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:455:9+102
    assume {:print "$at(2,21145,21247)"} true;
    goto L5;

    // label L3 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:455:86+23
L3:

    // $t16 := 10 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:455:86+23
    assume {:print "$at(2,21222,21245)"} true;
    $t16 := 10;
    assume $IsValid'u64'($t16);

    // $t17 := error::invalid_argument($t16) on_abort goto L7 with $t6 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:455:62+48
    call $t17 := $1_error_invalid_argument($t16);
    if ($abort_flag) {
        assume {:print "$at(2,21198,21246)"} true;
        $t6 := $abort_code;
        assume {:print "$track_abort(44,3):", $t6} $t6 == $t6;
        goto L7;
    }

    // trace_abort($t17) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:455:9+102
    assume {:print "$at(2,21145,21247)"} true;
    assume {:print "$track_abort(44,3):", $t17} $t17 == $t17;

    // $t6 := move($t17) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:455:9+102
    $t6 := $t17;

    // goto L7 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:455:9+102
    goto L7;

    // label L5 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:457:24+40
    assume {:print "$at(2,21273,21313)"} true;
L5:

    // $t4 := simple_map::create<string::String, vector<u8>>() on_abort goto L7 with $t6 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:457:24+40
    assume {:print "$at(2,21273,21313)"} true;
    call $t4 := $1_simple_map_create'$1_string_String_vec'u8''();
    if ($abort_flag) {
        assume {:print "$at(2,21273,21313)"} true;
        $t6 := $abort_code;
        assume {:print "$track_abort(44,3):", $t6} $t6 == $t6;
        goto L7;
    }

    // trace_local[metadata]($t4) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:457:13+8
    assume {:print "$track_local(44,3,4):", $t4} $t4 == $t4;

    // $t18 := borrow_local($t4) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:458:25+13
    assume {:print "$at(2,21339,21352)"} true;
    $t18 := $Mutation($Local(4), EmptyVec(), $t4);

    // $t19 := [109, 101, 116, 97, 100, 97, 116, 97, 95, 108, 111, 99, 97, 116, 105, 111, 110] at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:458:45+21
    $t19 := ConcatVec(ConcatVec(ConcatVec(ConcatVec(MakeVec4(109, 101, 116, 97), MakeVec4(100, 97, 116, 97)), MakeVec4(95, 108, 111, 99)), MakeVec4(97, 116, 105, 111)), MakeVec1(110));
    assume $IsValid'vec'u8''($t19);

    // $t20 := string::utf8($t19) on_abort goto L7 with $t6 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:458:40+27
    call $t20 := $1_string_utf8($t19);
    if ($abort_flag) {
        assume {:print "$at(2,21354,21381)"} true;
        $t6 := $abort_code;
        assume {:print "$track_abort(44,3):", $t6} $t6 == $t6;
        goto L7;
    }

    // simple_map::add<string::String, vector<u8>>($t18, $t20, $t0) on_abort goto L7 with $t6 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:458:9+78
    call $t18 := $1_simple_map_add'$1_string_String_vec'u8''($t18, $t20, $t0);
    if ($abort_flag) {
        assume {:print "$at(2,21323,21401)"} true;
        $t6 := $abort_code;
        assume {:print "$track_abort(44,3):", $t6} $t6 == $t6;
        goto L7;
    }

    // write_back[LocalRoot($t4)@]($t18) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:458:9+78
    $t4 := $Dereference($t18);

    // trace_local[metadata]($t4) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:458:9+78
    assume {:print "$track_local(44,3,4):", $t4} $t4 == $t4;

    // $t21 := borrow_local($t4) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:459:25+13
    assume {:print "$at(2,21427,21440)"} true;
    $t21 := $Mutation($Local(4), EmptyVec(), $t4);

    // $t22 := [109, 101, 116, 97, 100, 97, 116, 97, 95, 104, 97, 115, 104] at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:459:45+17
    $t22 := ConcatVec(ConcatVec(ConcatVec(MakeVec4(109, 101, 116, 97), MakeVec4(100, 97, 116, 97)), MakeVec4(95, 104, 97, 115)), MakeVec1(104));
    assume $IsValid'vec'u8''($t22);

    // $t23 := string::utf8($t22) on_abort goto L7 with $t6 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:459:40+23
    call $t23 := $1_string_utf8($t22);
    if ($abort_flag) {
        assume {:print "$at(2,21442,21465)"} true;
        $t6 := $abort_code;
        assume {:print "$track_abort(44,3):", $t6} $t6 == $t6;
        goto L7;
    }

    // simple_map::add<string::String, vector<u8>>($t21, $t23, $t1) on_abort goto L7 with $t6 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:459:9+70
    call $t21 := $1_simple_map_add'$1_string_String_vec'u8''($t21, $t23, $t1);
    if ($abort_flag) {
        assume {:print "$at(2,21411,21481)"} true;
        $t6 := $abort_code;
        assume {:print "$track_abort(44,3):", $t6} $t6 == $t6;
        goto L7;
    }

    // write_back[LocalRoot($t4)@]($t21) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:459:9+70
    $t4 := $Dereference($t21);

    // trace_local[metadata]($t4) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:459:9+70
    assume {:print "$track_local(44,3,4):", $t4} $t4 == $t4;

    // $t24 := move($t4) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:460:9+8
    assume {:print "$at(2,21491,21499)"} true;
    $t24 := $t4;

    // trace_return[0]($t24) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:460:9+8
    assume {:print "$track_return(44,3,0):", $t24} $t24 == $t24;

    // label L6 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:461:5+1
    assume {:print "$at(2,21504,21505)"} true;
L6:

    // assert Not(Gt(string::$length[](string::$utf8[]($t0)), 256)) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.spec.move:649:9+56
    assume {:print "$at(3,39438,39494)"} true;
    assert {:msg "assert_failed(3,39438,39494): function does not abort under this condition"}
      !($1_string_$length($1_string_$utf8($t0)) > 256);

    // assert Not(Gt(string::$length[](string::$utf8[]($t1)), 256)) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.spec.move:650:9+52
    assume {:print "$at(3,39503,39555)"} true;
    assert {:msg "assert_failed(3,39503,39555): function does not abort under this condition"}
      !($1_string_$length($1_string_$utf8($t1)) > 256);

    // assert Not(Not(string::spec_internal_check_utf8[]($t0))) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.spec.move:651:9+63
    assume {:print "$at(3,39564,39627)"} true;
    assert {:msg "assert_failed(3,39564,39627): function does not abort under this condition"}
      !!$1_string_spec_internal_check_utf8($t0);

    // assert Not(Not(string::spec_internal_check_utf8[]($t1))) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.spec.move:652:9+59
    assume {:print "$at(3,39636,39695)"} true;
    assert {:msg "assert_failed(3,39636,39695): function does not abort under this condition"}
      !!$1_string_spec_internal_check_utf8($t1);

    // assert Not(Not(string::spec_internal_check_utf8[]([109, 101, 116, 97, 100, 97, 116, 97, 95, 108, 111, 99, 97, 116, 105, 111, 110]))) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.spec.move:653:9+67
    assume {:print "$at(3,39704,39771)"} true;
    assert {:msg "assert_failed(3,39704,39771): function does not abort under this condition"}
      !!$1_string_spec_internal_check_utf8(ConcatVec(ConcatVec(ConcatVec(ConcatVec(MakeVec4(109, 101, 116, 97), MakeVec4(100, 97, 116, 97)), MakeVec4(95, 108, 111, 99)), MakeVec4(97, 116, 105, 111)), MakeVec1(110)));

    // assert Not(Not(string::spec_internal_check_utf8[]([109, 101, 116, 97, 100, 97, 116, 97, 95, 104, 97, 115, 104]))) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.spec.move:654:9+63
    assume {:print "$at(3,39780,39843)"} true;
    assert {:msg "assert_failed(3,39780,39843): function does not abort under this condition"}
      !!$1_string_spec_internal_check_utf8(ConcatVec(ConcatVec(ConcatVec(MakeVec4(109, 101, 116, 97), MakeVec4(100, 97, 116, 97)), MakeVec4(95, 104, 97, 115)), MakeVec1(104)));

    // return $t24 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.spec.move:654:9+63
    $ret0 := $t24;
    return;

    // label L7 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:461:5+1
    assume {:print "$at(2,21504,21505)"} true;
L7:

    // assert Or(Or(Or(Or(Or(Gt(string::$length[](string::$utf8[]($t0)), 256), Gt(string::$length[](string::$utf8[]($t1)), 256)), Not(string::spec_internal_check_utf8[]($t0))), Not(string::spec_internal_check_utf8[]($t1))), Not(string::spec_internal_check_utf8[]([109, 101, 116, 97, 100, 97, 116, 97, 95, 108, 111, 99, 97, 116, 105, 111, 110]))), Not(string::spec_internal_check_utf8[]([109, 101, 116, 97, 100, 97, 116, 97, 95, 104, 97, 115, 104]))) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.spec.move:646:5+571
    assume {:print "$at(3,39278,39849)"} true;
    assert {:msg "assert_failed(3,39278,39849): abort not covered by any of the `aborts_if` clauses"}
      (((((($1_string_$length($1_string_$utf8($t0)) > 256) || ($1_string_$length($1_string_$utf8($t1)) > 256)) || !$1_string_spec_internal_check_utf8($t0)) || !$1_string_spec_internal_check_utf8($t1)) || !$1_string_spec_internal_check_utf8(ConcatVec(ConcatVec(ConcatVec(ConcatVec(MakeVec4(109, 101, 116, 97), MakeVec4(100, 97, 116, 97)), MakeVec4(95, 108, 111, 99)), MakeVec4(97, 116, 105, 111)), MakeVec1(110)))) || !$1_string_spec_internal_check_utf8(ConcatVec(ConcatVec(ConcatVec(MakeVec4(109, 101, 116, 97), MakeVec4(100, 97, 116, 97)), MakeVec4(95, 104, 97, 115)), MakeVec1(104))));

    // abort($t6) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.spec.move:646:5+571
    $abort_code := $t6;
    $abort_flag := true;
    return;

}

// fun aptos_governance::get_voting_power [baseline] at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:433:5+788
procedure {:inline 1} $1_aptos_governance_get_voting_power(_$t0: int) returns ($ret0: int)
{
    // declare local variables
    var $t1: $1_staking_config_StakingConfig;
    var $t2: int;
    var $t3: int;
    var $t4: int;
    var $t5: $1_staking_config_StakingConfig;
    var $t6: bool;
    var $t7: $1_stake_StakePool;
    var $t8: $1_staking_config_StakingConfig;
    var $t9: int;
    var $t10: bool;
    var $t11: int;
    var $t12: int;
    var $t13: int;
    var $t14: int;
    var $t15: int;
    var $t0: int;
    var $temp_0'address': int;
    var $temp_0'u64': int;
    $t0 := _$t0;

    // bytecode translation starts here
    // assume Identical($t5, global<staking_config::StakingConfig>(1)) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.spec.move:617:9+77
    assume {:print "$at(3,37678,37755)"} true;
    assume ($t5 == $ResourceValue($1_staking_config_StakingConfig_$memory, 1));

    // assume Identical($t6, select staking_config::StakingConfig.allow_validator_set_change($t5)) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.spec.move:619:9+75
    assume {:print "$at(3,37840,37915)"} true;
    assume ($t6 == $allow_validator_set_change#$1_staking_config_StakingConfig($t5));

    // assume Identical($t7, global<stake::StakePool>($t0)) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.spec.move:620:9+56
    assume {:print "$at(3,37924,37980)"} true;
    assume ($t7 == $ResourceValue($1_stake_StakePool_$memory, $t0));

    // trace_local[pool_address]($t0) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:433:5+1
    assume {:print "$at(2,19660,19661)"} true;
    assume {:print "$track_local(44,10,0):", $t0} $t0 == $t0;

    // $t8 := staking_config::get() on_abort goto L4 with $t9 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:434:90+21
    assume {:print "$at(2,19800,19821)"} true;
    call $t8 := $1_staking_config_get();
    if ($abort_flag) {
        assume {:print "$at(2,19800,19821)"} true;
        $t9 := $abort_code;
        assume {:print "$track_abort(44,10):", $t9} $t9 == $t9;
        goto L4;
    }

    // $t10 := staking_config::get_allow_validator_set_change($t8) on_abort goto L4 with $t9 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:434:42+70
    call $t10 := $1_staking_config_get_allow_validator_set_change($t8);
    if ($abort_flag) {
        assume {:print "$at(2,19752,19822)"} true;
        $t9 := $abort_code;
        assume {:print "$track_abort(44,10):", $t9} $t9 == $t9;
        goto L4;
    }

    // if ($t10) goto L1 else goto L0 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:435:9+610
    assume {:print "$at(2,19832,20442)"} true;
    if ($t10) { goto L1; } else { goto L0; }

    // label L1 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:436:82+12
    assume {:print "$at(2,19947,19959)"} true;
L1:

    // ($t11, $t12, $t13, $t14) := stake::get_stake($t0) on_abort goto L4 with $t9 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:436:65+30
    assume {:print "$at(2,19930,19960)"} true;
    call $t11,$t12,$t13,$t14 := $1_stake_get_stake($t0);
    if ($abort_flag) {
        assume {:print "$at(2,19930,19960)"} true;
        $t9 := $abort_code;
        assume {:print "$track_abort(44,10):", $t9} $t9 == $t9;
        goto L4;
    }

    // trace_local[pending_inactive]($t14) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:436:45+16
    assume {:print "$track_local(44,10,4):", $t14} $t14 == $t14;

    // trace_local[pending_active]($t13) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:436:29+14
    assume {:print "$track_local(44,10,3):", $t13} $t13 == $t13;

    // destroy($t12) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:436:26+1

    // $t15 := +($t11, $t13) on_abort goto L4 with $t9 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:440:20+1
    assume {:print "$at(2,20316,20317)"} true;
    call $t15 := $AddU64($t11, $t13);
    if ($abort_flag) {
        assume {:print "$at(2,20316,20317)"} true;
        $t9 := $abort_code;
        assume {:print "$track_abort(44,10):", $t9} $t9 == $t9;
        goto L4;
    }

    // $t2 := +($t15, $t14) on_abort goto L4 with $t9 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:440:37+1
    call $t2 := $AddU64($t15, $t14);
    if ($abort_flag) {
        assume {:print "$at(2,20333,20334)"} true;
        $t9 := $abort_code;
        assume {:print "$track_abort(44,10):", $t9} $t9 == $t9;
        goto L4;
    }

    // goto L2 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:435:9+610
    assume {:print "$at(2,19832,20442)"} true;
    goto L2;

    // label L0 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:442:51+12
    assume {:print "$at(2,20419,20431)"} true;
L0:

    // $t2 := stake::get_current_epoch_voting_power($t0) on_abort goto L4 with $t9 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:442:13+51
    assume {:print "$at(2,20381,20432)"} true;
    call $t2 := $1_stake_get_current_epoch_voting_power($t0);
    if ($abort_flag) {
        assume {:print "$at(2,20381,20432)"} true;
        $t9 := $abort_code;
        assume {:print "$track_abort(44,10):", $t9} $t9 == $t9;
        goto L4;
    }

    // label L2 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:435:9+610
    assume {:print "$at(2,19832,20442)"} true;
L2:

    // trace_return[0]($t2) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:435:9+610
    assume {:print "$at(2,19832,20442)"} true;
    assume {:print "$track_return(44,10,0):", $t2} $t2 == $t2;

    // label L3 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:444:5+1
    assume {:print "$at(2,20447,20448)"} true;
L3:

    // return $t2 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:444:5+1
    assume {:print "$at(2,20447,20448)"} true;
    $ret0 := $t2;
    return;

    // label L4 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:444:5+1
L4:

    // abort($t9) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:444:5+1
    assume {:print "$at(2,20447,20448)"} true;
    $abort_code := $t9;
    $abort_flag := true;
    return;

}

// fun aptos_governance::get_voting_power [verification] at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:433:5+788
procedure {:timeLimit 40} $1_aptos_governance_get_voting_power$verify(_$t0: int) returns ($ret0: int)
{
    // declare local variables
    var $t1: $1_staking_config_StakingConfig;
    var $t2: int;
    var $t3: int;
    var $t4: int;
    var $t5: $1_staking_config_StakingConfig;
    var $t6: bool;
    var $t7: $1_stake_StakePool;
    var $t8: $1_staking_config_StakingConfig;
    var $t9: int;
    var $t10: bool;
    var $t11: int;
    var $t12: int;
    var $t13: int;
    var $t14: int;
    var $t15: int;
    var $t0: int;
    var $temp_0'address': int;
    var $temp_0'u64': int;
    var $1_staking_config_StakingConfig_$memory#18: $Memory $1_staking_config_StakingConfig;
    var $1_stake_StakePool_$memory#19: $Memory $1_stake_StakePool;
    var $1_stake_ValidatorSet_$memory#20: $Memory $1_stake_ValidatorSet;
    $t0 := _$t0;

    // verification entrypoint assumptions
    call $InitVerification();

    // bytecode translation starts here
    // assume WellFormed($t0) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:433:5+1
    assume {:print "$at(2,19660,19661)"} true;
    assume $IsValid'address'($t0);

    // assume forall $rsc: ResourceDomain<chain_status::GenesisEndMarker>(): WellFormed($rsc) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:433:5+1
    assume (forall $a_0: int :: {$ResourceValue($1_chain_status_GenesisEndMarker_$memory, $a_0)}(var $rsc := $ResourceValue($1_chain_status_GenesisEndMarker_$memory, $a_0);
    ($IsValid'$1_chain_status_GenesisEndMarker'($rsc))));

    // assume forall $rsc: ResourceDomain<staking_config::StakingConfig>(): And(WellFormed($rsc), And(And(Le(select staking_config::StakingConfig.rewards_rate($rsc), 1000000), Gt(select staking_config::StakingConfig.rewards_rate_denominator($rsc), 0)), Le(select staking_config::StakingConfig.rewards_rate($rsc), select staking_config::StakingConfig.rewards_rate_denominator($rsc)))) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:433:5+1
    assume (forall $a_0: int :: {$ResourceValue($1_staking_config_StakingConfig_$memory, $a_0)}(var $rsc := $ResourceValue($1_staking_config_StakingConfig_$memory, $a_0);
    (($IsValid'$1_staking_config_StakingConfig'($rsc) && ((($rewards_rate#$1_staking_config_StakingConfig($rsc) <= 1000000) && ($rewards_rate_denominator#$1_staking_config_StakingConfig($rsc) > 0)) && ($rewards_rate#$1_staking_config_StakingConfig($rsc) <= $rewards_rate_denominator#$1_staking_config_StakingConfig($rsc)))))));

    // assume forall $rsc: ResourceDomain<stake::StakePool>(): WellFormed($rsc) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:433:5+1
    assume (forall $a_0: int :: {$ResourceValue($1_stake_StakePool_$memory, $a_0)}(var $rsc := $ResourceValue($1_stake_StakePool_$memory, $a_0);
    ($IsValid'$1_stake_StakePool'($rsc))));

    // assume forall $rsc: ResourceDomain<stake::ValidatorConfig>(): WellFormed($rsc) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:433:5+1
    assume (forall $a_0: int :: {$ResourceValue($1_stake_ValidatorConfig_$memory, $a_0)}(var $rsc := $ResourceValue($1_stake_ValidatorConfig_$memory, $a_0);
    ($IsValid'$1_stake_ValidatorConfig'($rsc))));

    // assume forall $rsc: ResourceDomain<stake::ValidatorPerformance>(): WellFormed($rsc) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:433:5+1
    assume (forall $a_0: int :: {$ResourceValue($1_stake_ValidatorPerformance_$memory, $a_0)}(var $rsc := $ResourceValue($1_stake_ValidatorPerformance_$memory, $a_0);
    ($IsValid'$1_stake_ValidatorPerformance'($rsc))));

    // assume forall $rsc: ResourceDomain<stake::ValidatorSet>(): WellFormed($rsc) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:433:5+1
    assume (forall $a_0: int :: {$ResourceValue($1_stake_ValidatorSet_$memory, $a_0)}(var $rsc := $ResourceValue($1_stake_ValidatorSet_$memory, $a_0);
    ($IsValid'$1_stake_ValidatorSet'($rsc))));

    // assume Implies(chain_status::$is_operating(), exists<staking_config::StakingConfig>(1)) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:433:5+788
    // global invariant at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/configs/staking_config.spec.move:4:9+83
    assume ($1_chain_status_$is_operating($1_chain_status_GenesisEndMarker_$memory) ==> $ResourceExists($1_staking_config_StakingConfig_$memory, 1));

    // assume Implies(exists<stake::ValidatorSet>(1), stake::validator_set_is_valid()) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:433:5+788
    // global invariant at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/stake.spec.move:8:9+92
    assume ($ResourceExists($1_stake_ValidatorSet_$memory, 1) ==> $1_stake_validator_set_is_valid($1_stake_StakePool_$memory, $1_stake_ValidatorConfig_$memory, $1_stake_ValidatorPerformance_$memory, $1_stake_ValidatorSet_$memory));

    // assume Implies(chain_status::$is_operating(), exists<stake::ValidatorSet>(1)) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:433:5+788
    // global invariant at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/stake.spec.move:12:9+96
    assume ($1_chain_status_$is_operating($1_chain_status_GenesisEndMarker_$memory) ==> $ResourceExists($1_stake_ValidatorSet_$memory, 1));

    // assume Identical($t5, global<staking_config::StakingConfig>(1)) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.spec.move:617:9+77
    assume {:print "$at(3,37678,37755)"} true;
    assume ($t5 == $ResourceValue($1_staking_config_StakingConfig_$memory, 1));

    // assume Identical($t6, select staking_config::StakingConfig.allow_validator_set_change($t5)) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.spec.move:619:9+75
    assume {:print "$at(3,37840,37915)"} true;
    assume ($t6 == $allow_validator_set_change#$1_staking_config_StakingConfig($t5));

    // assume Identical($t7, global<stake::StakePool>($t0)) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.spec.move:620:9+56
    assume {:print "$at(3,37924,37980)"} true;
    assume ($t7 == $ResourceValue($1_stake_StakePool_$memory, $t0));

    // @18 := save_mem(staking_config::StakingConfig) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:433:5+1
    assume {:print "$at(2,19660,19661)"} true;
    $1_staking_config_StakingConfig_$memory#18 := $1_staking_config_StakingConfig_$memory;

    // @19 := save_mem(stake::StakePool) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:433:5+1
    $1_stake_StakePool_$memory#19 := $1_stake_StakePool_$memory;

    // @20 := save_mem(stake::ValidatorSet) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:433:5+1
    $1_stake_ValidatorSet_$memory#20 := $1_stake_ValidatorSet_$memory;

    // trace_local[pool_address]($t0) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:433:5+1
    assume {:print "$track_local(44,10,0):", $t0} $t0 == $t0;

    // $t8 := staking_config::get() on_abort goto L4 with $t9 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:434:90+21
    assume {:print "$at(2,19800,19821)"} true;
    call $t8 := $1_staking_config_get();
    if ($abort_flag) {
        assume {:print "$at(2,19800,19821)"} true;
        $t9 := $abort_code;
        assume {:print "$track_abort(44,10):", $t9} $t9 == $t9;
        goto L4;
    }

    // $t10 := staking_config::get_allow_validator_set_change($t8) on_abort goto L4 with $t9 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:434:42+70
    call $t10 := $1_staking_config_get_allow_validator_set_change($t8);
    if ($abort_flag) {
        assume {:print "$at(2,19752,19822)"} true;
        $t9 := $abort_code;
        assume {:print "$track_abort(44,10):", $t9} $t9 == $t9;
        goto L4;
    }

    // if ($t10) goto L1 else goto L0 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:435:9+610
    assume {:print "$at(2,19832,20442)"} true;
    if ($t10) { goto L1; } else { goto L0; }

    // label L1 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:436:82+12
    assume {:print "$at(2,19947,19959)"} true;
L1:

    // ($t11, $t12, $t13, $t14) := stake::get_stake($t0) on_abort goto L4 with $t9 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:436:65+30
    assume {:print "$at(2,19930,19960)"} true;
    call $t11,$t12,$t13,$t14 := $1_stake_get_stake($t0);
    if ($abort_flag) {
        assume {:print "$at(2,19930,19960)"} true;
        $t9 := $abort_code;
        assume {:print "$track_abort(44,10):", $t9} $t9 == $t9;
        goto L4;
    }

    // trace_local[pending_inactive]($t14) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:436:45+16
    assume {:print "$track_local(44,10,4):", $t14} $t14 == $t14;

    // trace_local[pending_active]($t13) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:436:29+14
    assume {:print "$track_local(44,10,3):", $t13} $t13 == $t13;

    // destroy($t12) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:436:26+1

    // $t15 := +($t11, $t13) on_abort goto L4 with $t9 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:440:20+1
    assume {:print "$at(2,20316,20317)"} true;
    call $t15 := $AddU64($t11, $t13);
    if ($abort_flag) {
        assume {:print "$at(2,20316,20317)"} true;
        $t9 := $abort_code;
        assume {:print "$track_abort(44,10):", $t9} $t9 == $t9;
        goto L4;
    }

    // $t2 := +($t15, $t14) on_abort goto L4 with $t9 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:440:37+1
    call $t2 := $AddU64($t15, $t14);
    if ($abort_flag) {
        assume {:print "$at(2,20333,20334)"} true;
        $t9 := $abort_code;
        assume {:print "$track_abort(44,10):", $t9} $t9 == $t9;
        goto L4;
    }

    // goto L2 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:435:9+610
    assume {:print "$at(2,19832,20442)"} true;
    goto L2;

    // label L0 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:442:51+12
    assume {:print "$at(2,20419,20431)"} true;
L0:

    // $t2 := stake::get_current_epoch_voting_power($t0) on_abort goto L4 with $t9 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:442:13+51
    assume {:print "$at(2,20381,20432)"} true;
    call $t2 := $1_stake_get_current_epoch_voting_power($t0);
    if ($abort_flag) {
        assume {:print "$at(2,20381,20432)"} true;
        $t9 := $abort_code;
        assume {:print "$track_abort(44,10):", $t9} $t9 == $t9;
        goto L4;
    }

    // label L2 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:435:9+610
    assume {:print "$at(2,19832,20442)"} true;
L2:

    // trace_return[0]($t2) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:435:9+610
    assume {:print "$at(2,19832,20442)"} true;
    assume {:print "$track_return(44,10,0):", $t2} $t2 == $t2;

    // label L3 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:444:5+1
    assume {:print "$at(2,20447,20448)"} true;
L3:

    // assert Not(Not(exists[@18]<staking_config::StakingConfig>(1))) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.spec.move:618:9+67
    assume {:print "$at(3,37764,37831)"} true;
    assert {:msg "assert_failed(3,37764,37831): function does not abort under this condition"}
      !!$ResourceExists($1_staking_config_StakingConfig_$memory#18, 1);

    // assert Not(And($t6, Gt(Add(Add(select coin::Coin.value(select stake::StakePool.active($t7)), select coin::Coin.value(select stake::StakePool.pending_active($t7))), select coin::Coin.value(select stake::StakePool.pending_inactive($t7))), 18446744073709551615))) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.spec.move:621:9+146
    assume {:print "$at(3,37989,38135)"} true;
    assert {:msg "assert_failed(3,37989,38135): function does not abort under this condition"}
      !($t6 && ((($value#$1_coin_Coin'$1_aptos_coin_AptosCoin'($active#$1_stake_StakePool($t7)) + $value#$1_coin_Coin'$1_aptos_coin_AptosCoin'($pending_active#$1_stake_StakePool($t7))) + $value#$1_coin_Coin'$1_aptos_coin_AptosCoin'($pending_inactive#$1_stake_StakePool($t7))) > 18446744073709551615));

    // assert Not(Not(exists[@19]<stake::StakePool>($t0))) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.spec.move:622:9+50
    assume {:print "$at(3,38144,38194)"} true;
    assert {:msg "assert_failed(3,38144,38194): function does not abort under this condition"}
      !!$ResourceExists($1_stake_StakePool_$memory#19, $t0);

    // assert Not(And(Not($t6), Not(exists[@20]<stake::ValidatorSet>(1)))) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.spec.move:623:9+88
    assume {:print "$at(3,38203,38291)"} true;
    assert {:msg "assert_failed(3,38203,38291): function does not abort under this condition"}
      !(!$t6 && !$ResourceExists($1_stake_ValidatorSet_$memory#20, 1));

    // assert Not(And(And(Not($t6), stake::spec_is_current_epoch_validator[@20]($t0)), Gt(Add(select coin::Coin.value(select stake::StakePool.active($t7)), select coin::Coin.value(select stake::StakePool.pending_inactive($t7))), 18446744073709551615))) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.spec.move:624:9+167
    assume {:print "$at(3,38300,38467)"} true;
    assert {:msg "assert_failed(3,38300,38467): function does not abort under this condition"}
      !((!$t6 && $1_stake_spec_is_current_epoch_validator($1_stake_ValidatorSet_$memory#20, $t0)) && (($value#$1_coin_Coin'$1_aptos_coin_AptosCoin'($active#$1_stake_StakePool($t7)) + $value#$1_coin_Coin'$1_aptos_coin_AptosCoin'($pending_inactive#$1_stake_StakePool($t7))) > 18446744073709551615));

    // assert Implies($t6, Eq<u64>($t2, Add(Add(select coin::Coin.value(select stake::StakePool.active($t7)), select coin::Coin.value(select stake::StakePool.pending_active($t7))), select coin::Coin.value(select stake::StakePool.pending_inactive($t7))))) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.spec.move:626:9+143
    assume {:print "$at(3,38477,38620)"} true;
    assert {:msg "assert_failed(3,38477,38620): post-condition does not hold"}
      ($t6 ==> $IsEqual'u64'($t2, (($value#$1_coin_Coin'$1_aptos_coin_AptosCoin'($active#$1_stake_StakePool($t7)) + $value#$1_coin_Coin'$1_aptos_coin_AptosCoin'($pending_active#$1_stake_StakePool($t7))) + $value#$1_coin_Coin'$1_aptos_coin_AptosCoin'($pending_inactive#$1_stake_StakePool($t7)))));

    // assert Implies(Not($t6), (if stake::spec_is_current_epoch_validator($t0) {Eq<u64>($t2, Add(select coin::Coin.value(select stake::StakePool.active($t7)), select coin::Coin.value(select stake::StakePool.pending_inactive($t7))))} else {Eq<u64>($t2, 0)})) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.spec.move:627:9+233
    assume {:print "$at(3,38629,38862)"} true;
    assert {:msg "assert_failed(3,38629,38862): post-condition does not hold"}
      (!$t6 ==> (if ($1_stake_spec_is_current_epoch_validator($1_stake_ValidatorSet_$memory, $t0)) then ($IsEqual'u64'($t2, ($value#$1_coin_Coin'$1_aptos_coin_AptosCoin'($active#$1_stake_StakePool($t7)) + $value#$1_coin_Coin'$1_aptos_coin_AptosCoin'($pending_inactive#$1_stake_StakePool($t7))))) else ($IsEqual'u64'($t2, 0))));

    // return $t2 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.spec.move:627:9+233
    $ret0 := $t2;
    return;

    // label L4 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.move:444:5+1
    assume {:print "$at(2,20447,20448)"} true;
L4:

    // assert Or(Or(Or(Or(Not(exists[@18]<staking_config::StakingConfig>(1)), And($t6, Gt(Add(Add(select coin::Coin.value(select stake::StakePool.active($t7)), select coin::Coin.value(select stake::StakePool.pending_active($t7))), select coin::Coin.value(select stake::StakePool.pending_inactive($t7))), 18446744073709551615))), Not(exists[@19]<stake::StakePool>($t0))), And(Not($t6), Not(exists[@20]<stake::ValidatorSet>(1)))), And(And(Not($t6), stake::spec_is_current_epoch_validator[@20]($t0)), Gt(Add(select coin::Coin.value(select stake::StakePool.active($t7)), select coin::Coin.value(select stake::StakePool.pending_inactive($t7))), 18446744073709551615))) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.spec.move:609:5+1668
    assume {:print "$at(3,37200,38868)"} true;
    assert {:msg "assert_failed(3,37200,38868): abort not covered by any of the `aborts_if` clauses"}
      ((((!$ResourceExists($1_staking_config_StakingConfig_$memory#18, 1) || ($t6 && ((($value#$1_coin_Coin'$1_aptos_coin_AptosCoin'($active#$1_stake_StakePool($t7)) + $value#$1_coin_Coin'$1_aptos_coin_AptosCoin'($pending_active#$1_stake_StakePool($t7))) + $value#$1_coin_Coin'$1_aptos_coin_AptosCoin'($pending_inactive#$1_stake_StakePool($t7))) > 18446744073709551615))) || !$ResourceExists($1_stake_StakePool_$memory#19, $t0)) || (!$t6 && !$ResourceExists($1_stake_ValidatorSet_$memory#20, 1))) || ((!$t6 && $1_stake_spec_is_current_epoch_validator($1_stake_ValidatorSet_$memory#20, $t0)) && (($value#$1_coin_Coin'$1_aptos_coin_AptosCoin'($active#$1_stake_StakePool($t7)) + $value#$1_coin_Coin'$1_aptos_coin_AptosCoin'($pending_inactive#$1_stake_StakePool($t7))) > 18446744073709551615)));

    // abort($t9) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_governance.spec.move:609:5+1668
    $abort_code := $t9;
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
