
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
// Native Vector implementation for element type `$1_aptos_coin_DelegatedMintCapability`

// Not inlined. It appears faster this way.
function $IsEqual'vec'$1_aptos_coin_DelegatedMintCapability''(v1: Vec ($1_aptos_coin_DelegatedMintCapability), v2: Vec ($1_aptos_coin_DelegatedMintCapability)): bool {
    LenVec(v1) == LenVec(v2) &&
    (forall i: int:: InRangeVec(v1, i) ==> $IsEqual'$1_aptos_coin_DelegatedMintCapability'(ReadVec(v1, i), ReadVec(v2, i)))
}

// Not inlined.
function $IsPrefix'vec'$1_aptos_coin_DelegatedMintCapability''(v: Vec ($1_aptos_coin_DelegatedMintCapability), prefix: Vec ($1_aptos_coin_DelegatedMintCapability)): bool {
    LenVec(v) >= LenVec(prefix) &&
    (forall i: int:: InRangeVec(prefix, i) ==> $IsEqual'$1_aptos_coin_DelegatedMintCapability'(ReadVec(v, i), ReadVec(prefix, i)))
}

// Not inlined.
function $IsSuffix'vec'$1_aptos_coin_DelegatedMintCapability''(v: Vec ($1_aptos_coin_DelegatedMintCapability), suffix: Vec ($1_aptos_coin_DelegatedMintCapability)): bool {
    LenVec(v) >= LenVec(suffix) &&
    (forall i: int:: InRangeVec(suffix, i) ==> $IsEqual'$1_aptos_coin_DelegatedMintCapability'(ReadVec(v, LenVec(v) - LenVec(suffix) + i), ReadVec(suffix, i)))
}

// Not inlined.
function $IsValid'vec'$1_aptos_coin_DelegatedMintCapability''(v: Vec ($1_aptos_coin_DelegatedMintCapability)): bool {
    $IsValid'u64'(LenVec(v)) &&
    (forall i: int:: InRangeVec(v, i) ==> $IsValid'$1_aptos_coin_DelegatedMintCapability'(ReadVec(v, i)))
}


function {:inline} $ContainsVec'$1_aptos_coin_DelegatedMintCapability'(v: Vec ($1_aptos_coin_DelegatedMintCapability), e: $1_aptos_coin_DelegatedMintCapability): bool {
    (exists i: int :: $IsValid'u64'(i) && InRangeVec(v, i) && $IsEqual'$1_aptos_coin_DelegatedMintCapability'(ReadVec(v, i), e))
}

function $IndexOfVec'$1_aptos_coin_DelegatedMintCapability'(v: Vec ($1_aptos_coin_DelegatedMintCapability), e: $1_aptos_coin_DelegatedMintCapability): int;
axiom (forall v: Vec ($1_aptos_coin_DelegatedMintCapability), e: $1_aptos_coin_DelegatedMintCapability:: {$IndexOfVec'$1_aptos_coin_DelegatedMintCapability'(v, e)}
    (var i := $IndexOfVec'$1_aptos_coin_DelegatedMintCapability'(v, e);
     if (!$ContainsVec'$1_aptos_coin_DelegatedMintCapability'(v, e)) then i == -1
     else $IsValid'u64'(i) && InRangeVec(v, i) && $IsEqual'$1_aptos_coin_DelegatedMintCapability'(ReadVec(v, i), e) &&
        (forall j: int :: $IsValid'u64'(j) && j >= 0 && j < i ==> !$IsEqual'$1_aptos_coin_DelegatedMintCapability'(ReadVec(v, j), e))));


function {:inline} $RangeVec'$1_aptos_coin_DelegatedMintCapability'(v: Vec ($1_aptos_coin_DelegatedMintCapability)): $Range {
    $Range(0, LenVec(v))
}


function {:inline} $EmptyVec'$1_aptos_coin_DelegatedMintCapability'(): Vec ($1_aptos_coin_DelegatedMintCapability) {
    EmptyVec()
}

procedure {:inline 1} $1_vector_empty'$1_aptos_coin_DelegatedMintCapability'() returns (v: Vec ($1_aptos_coin_DelegatedMintCapability)) {
    v := EmptyVec();
}

function {:inline} $1_vector_$empty'$1_aptos_coin_DelegatedMintCapability'(): Vec ($1_aptos_coin_DelegatedMintCapability) {
    EmptyVec()
}

procedure {:inline 1} $1_vector_is_empty'$1_aptos_coin_DelegatedMintCapability'(v: Vec ($1_aptos_coin_DelegatedMintCapability)) returns (b: bool) {
    b := IsEmptyVec(v);
}

procedure {:inline 1} $1_vector_push_back'$1_aptos_coin_DelegatedMintCapability'(m: $Mutation (Vec ($1_aptos_coin_DelegatedMintCapability)), val: $1_aptos_coin_DelegatedMintCapability) returns (m': $Mutation (Vec ($1_aptos_coin_DelegatedMintCapability))) {
    m' := $UpdateMutation(m, ExtendVec($Dereference(m), val));
}

function {:inline} $1_vector_$push_back'$1_aptos_coin_DelegatedMintCapability'(v: Vec ($1_aptos_coin_DelegatedMintCapability), val: $1_aptos_coin_DelegatedMintCapability): Vec ($1_aptos_coin_DelegatedMintCapability) {
    ExtendVec(v, val)
}

procedure {:inline 1} $1_vector_pop_back'$1_aptos_coin_DelegatedMintCapability'(m: $Mutation (Vec ($1_aptos_coin_DelegatedMintCapability))) returns (e: $1_aptos_coin_DelegatedMintCapability, m': $Mutation (Vec ($1_aptos_coin_DelegatedMintCapability))) {
    var v: Vec ($1_aptos_coin_DelegatedMintCapability);
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

procedure {:inline 1} $1_vector_append'$1_aptos_coin_DelegatedMintCapability'(m: $Mutation (Vec ($1_aptos_coin_DelegatedMintCapability)), other: Vec ($1_aptos_coin_DelegatedMintCapability)) returns (m': $Mutation (Vec ($1_aptos_coin_DelegatedMintCapability))) {
    m' := $UpdateMutation(m, ConcatVec($Dereference(m), other));
}

procedure {:inline 1} $1_vector_reverse'$1_aptos_coin_DelegatedMintCapability'(m: $Mutation (Vec ($1_aptos_coin_DelegatedMintCapability))) returns (m': $Mutation (Vec ($1_aptos_coin_DelegatedMintCapability))) {
    m' := $UpdateMutation(m, ReverseVec($Dereference(m)));
}

procedure {:inline 1} $1_vector_reverse_append'$1_aptos_coin_DelegatedMintCapability'(m: $Mutation (Vec ($1_aptos_coin_DelegatedMintCapability)), other: Vec ($1_aptos_coin_DelegatedMintCapability)) returns (m': $Mutation (Vec ($1_aptos_coin_DelegatedMintCapability))) {
    m' := $UpdateMutation(m, ConcatVec($Dereference(m), ReverseVec(other)));
}

procedure {:inline 1} $1_vector_trim_reverse'$1_aptos_coin_DelegatedMintCapability'(m: $Mutation (Vec ($1_aptos_coin_DelegatedMintCapability)), new_len: int) returns (v: (Vec ($1_aptos_coin_DelegatedMintCapability)), m': $Mutation (Vec ($1_aptos_coin_DelegatedMintCapability))) {
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

procedure {:inline 1} $1_vector_trim'$1_aptos_coin_DelegatedMintCapability'(m: $Mutation (Vec ($1_aptos_coin_DelegatedMintCapability)), new_len: int) returns (v: (Vec ($1_aptos_coin_DelegatedMintCapability)), m': $Mutation (Vec ($1_aptos_coin_DelegatedMintCapability))) {
    var len: int;
    v := $Dereference(m);
    if (LenVec(v) < new_len) {
        call $ExecFailureAbort();
        return;
    }
    v := SliceVec(v, new_len, LenVec(v));
    m' := $UpdateMutation(m, SliceVec($Dereference(m), 0, new_len));
}

procedure {:inline 1} $1_vector_reverse_slice'$1_aptos_coin_DelegatedMintCapability'(m: $Mutation (Vec ($1_aptos_coin_DelegatedMintCapability)), left: int, right: int) returns (m': $Mutation (Vec ($1_aptos_coin_DelegatedMintCapability))) {
    var left_vec: Vec ($1_aptos_coin_DelegatedMintCapability);
    var mid_vec: Vec ($1_aptos_coin_DelegatedMintCapability);
    var right_vec: Vec ($1_aptos_coin_DelegatedMintCapability);
    var v: Vec ($1_aptos_coin_DelegatedMintCapability);
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

procedure {:inline 1} $1_vector_rotate'$1_aptos_coin_DelegatedMintCapability'(m: $Mutation (Vec ($1_aptos_coin_DelegatedMintCapability)), rot: int) returns (n: int, m': $Mutation (Vec ($1_aptos_coin_DelegatedMintCapability))) {
    var v: Vec ($1_aptos_coin_DelegatedMintCapability);
    var len: int;
    var left_vec: Vec ($1_aptos_coin_DelegatedMintCapability);
    var right_vec: Vec ($1_aptos_coin_DelegatedMintCapability);
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

procedure {:inline 1} $1_vector_rotate_slice'$1_aptos_coin_DelegatedMintCapability'(m: $Mutation (Vec ($1_aptos_coin_DelegatedMintCapability)), left: int, rot: int, right: int) returns (n: int, m': $Mutation (Vec ($1_aptos_coin_DelegatedMintCapability))) {
    var left_vec: Vec ($1_aptos_coin_DelegatedMintCapability);
    var mid_vec: Vec ($1_aptos_coin_DelegatedMintCapability);
    var right_vec: Vec ($1_aptos_coin_DelegatedMintCapability);
    var mid_left_vec: Vec ($1_aptos_coin_DelegatedMintCapability);
    var mid_right_vec: Vec ($1_aptos_coin_DelegatedMintCapability);
    var v: Vec ($1_aptos_coin_DelegatedMintCapability);
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

procedure {:inline 1} $1_vector_insert'$1_aptos_coin_DelegatedMintCapability'(m: $Mutation (Vec ($1_aptos_coin_DelegatedMintCapability)), i: int, e: $1_aptos_coin_DelegatedMintCapability) returns (m': $Mutation (Vec ($1_aptos_coin_DelegatedMintCapability))) {
    var left_vec: Vec ($1_aptos_coin_DelegatedMintCapability);
    var right_vec: Vec ($1_aptos_coin_DelegatedMintCapability);
    var v: Vec ($1_aptos_coin_DelegatedMintCapability);
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

procedure {:inline 1} $1_vector_length'$1_aptos_coin_DelegatedMintCapability'(v: Vec ($1_aptos_coin_DelegatedMintCapability)) returns (l: int) {
    l := LenVec(v);
}

function {:inline} $1_vector_$length'$1_aptos_coin_DelegatedMintCapability'(v: Vec ($1_aptos_coin_DelegatedMintCapability)): int {
    LenVec(v)
}

procedure {:inline 1} $1_vector_borrow'$1_aptos_coin_DelegatedMintCapability'(v: Vec ($1_aptos_coin_DelegatedMintCapability), i: int) returns (dst: $1_aptos_coin_DelegatedMintCapability) {
    if (!InRangeVec(v, i)) {
        call $ExecFailureAbort();
        return;
    }
    dst := ReadVec(v, i);
}

function {:inline} $1_vector_$borrow'$1_aptos_coin_DelegatedMintCapability'(v: Vec ($1_aptos_coin_DelegatedMintCapability), i: int): $1_aptos_coin_DelegatedMintCapability {
    ReadVec(v, i)
}

procedure {:inline 1} $1_vector_borrow_mut'$1_aptos_coin_DelegatedMintCapability'(m: $Mutation (Vec ($1_aptos_coin_DelegatedMintCapability)), index: int)
returns (dst: $Mutation ($1_aptos_coin_DelegatedMintCapability), m': $Mutation (Vec ($1_aptos_coin_DelegatedMintCapability)))
{
    var v: Vec ($1_aptos_coin_DelegatedMintCapability);
    v := $Dereference(m);
    if (!InRangeVec(v, index)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Mutation(l#$Mutation(m), ExtendVec(p#$Mutation(m), index), ReadVec(v, index));
    m' := m;
}

function {:inline} $1_vector_$borrow_mut'$1_aptos_coin_DelegatedMintCapability'(v: Vec ($1_aptos_coin_DelegatedMintCapability), i: int): $1_aptos_coin_DelegatedMintCapability {
    ReadVec(v, i)
}

procedure {:inline 1} $1_vector_destroy_empty'$1_aptos_coin_DelegatedMintCapability'(v: Vec ($1_aptos_coin_DelegatedMintCapability)) {
    if (!IsEmptyVec(v)) {
      call $ExecFailureAbort();
    }
}

procedure {:inline 1} $1_vector_swap'$1_aptos_coin_DelegatedMintCapability'(m: $Mutation (Vec ($1_aptos_coin_DelegatedMintCapability)), i: int, j: int) returns (m': $Mutation (Vec ($1_aptos_coin_DelegatedMintCapability)))
{
    var v: Vec ($1_aptos_coin_DelegatedMintCapability);
    v := $Dereference(m);
    if (!InRangeVec(v, i) || !InRangeVec(v, j)) {
        call $ExecFailureAbort();
        return;
    }
    m' := $UpdateMutation(m, SwapVec(v, i, j));
}

function {:inline} $1_vector_$swap'$1_aptos_coin_DelegatedMintCapability'(v: Vec ($1_aptos_coin_DelegatedMintCapability), i: int, j: int): Vec ($1_aptos_coin_DelegatedMintCapability) {
    SwapVec(v, i, j)
}

procedure {:inline 1} $1_vector_remove'$1_aptos_coin_DelegatedMintCapability'(m: $Mutation (Vec ($1_aptos_coin_DelegatedMintCapability)), i: int) returns (e: $1_aptos_coin_DelegatedMintCapability, m': $Mutation (Vec ($1_aptos_coin_DelegatedMintCapability)))
{
    var v: Vec ($1_aptos_coin_DelegatedMintCapability);

    v := $Dereference(m);

    if (!InRangeVec(v, i)) {
        call $ExecFailureAbort();
        return;
    }
    e := ReadVec(v, i);
    m' := $UpdateMutation(m, RemoveAtVec(v, i));
}

procedure {:inline 1} $1_vector_swap_remove'$1_aptos_coin_DelegatedMintCapability'(m: $Mutation (Vec ($1_aptos_coin_DelegatedMintCapability)), i: int) returns (e: $1_aptos_coin_DelegatedMintCapability, m': $Mutation (Vec ($1_aptos_coin_DelegatedMintCapability)))
{
    var len: int;
    var v: Vec ($1_aptos_coin_DelegatedMintCapability);

    v := $Dereference(m);
    len := LenVec(v);
    if (!InRangeVec(v, i)) {
        call $ExecFailureAbort();
        return;
    }
    e := ReadVec(v, i);
    m' := $UpdateMutation(m, RemoveVec(SwapVec(v, i, len-1)));
}

procedure {:inline 1} $1_vector_contains'$1_aptos_coin_DelegatedMintCapability'(v: Vec ($1_aptos_coin_DelegatedMintCapability), e: $1_aptos_coin_DelegatedMintCapability) returns (res: bool)  {
    res := $ContainsVec'$1_aptos_coin_DelegatedMintCapability'(v, e);
}

procedure {:inline 1}
$1_vector_index_of'$1_aptos_coin_DelegatedMintCapability'(v: Vec ($1_aptos_coin_DelegatedMintCapability), e: $1_aptos_coin_DelegatedMintCapability) returns (res1: bool, res2: int) {
    res2 := $IndexOfVec'$1_aptos_coin_DelegatedMintCapability'(v, e);
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
// Native Table key encoding for type `address`

function $EncodeKey'address'(k: int): int;
axiom (
  forall k1, k2: int :: {$EncodeKey'address'(k1), $EncodeKey'address'(k2)}
    $IsEqual'address'(k1, k2) <==> $EncodeKey'address'(k1) == $EncodeKey'address'(k2)
);


// ----------------------------------------------------------------------------------
// Native Table implementation for type `(address,u128)`

function $IsEqual'$1_table_Table'address_u128''(t1: Table int (int), t2: Table int (int)): bool {
    LenTable(t1) == LenTable(t2) &&
    (forall k: int :: ContainsTable(t1, k) <==> ContainsTable(t2, k)) &&
    (forall k: int :: ContainsTable(t1, k) ==> GetTable(t1, k) == GetTable(t2, k)) &&
    (forall k: int :: ContainsTable(t2, k) ==> GetTable(t1, k) == GetTable(t2, k))
}

// Not inlined.
function $IsValid'$1_table_Table'address_u128''(t: Table int (int)): bool {
    $IsValid'u64'(LenTable(t)) &&
    (forall i: int:: ContainsTable(t, i) ==> $IsValid'u128'(GetTable(t, i)))
}
procedure {:inline 2} $1_table_new'address_u128'() returns (v: Table int (int)) {
    v := EmptyTable();
}
procedure {:inline 2} $1_table_destroy'address_u128'(t: Table int (int)) {
    if (LenTable(t) != 0) {
        call $Abort($StdError(1/*INVALID_STATE*/, 102/*ENOT_EMPTY*/));
    }
}
procedure {:inline 2} $1_table_contains'address_u128'(t: (Table int (int)), k: int) returns (r: bool) {
    r := ContainsTable(t, $EncodeKey'address'(k));
}
procedure {:inline 2} $1_table_add'address_u128'(m: $Mutation (Table int (int)), k: int, v: int) returns (m': $Mutation(Table int (int))) {
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
procedure {:inline 2} $1_table_upsert'address_u128'(m: $Mutation (Table int (int)), k: int, v: int) returns (m': $Mutation(Table int (int))) {
    var enc_k: int;
    var t: Table int (int);
    enc_k := $EncodeKey'address'(k);
    t := $Dereference(m);
    if (ContainsTable(t, enc_k)) {
        m' := $UpdateMutation(m, UpdateTable(t, enc_k, v));
    } else {
        m' := $UpdateMutation(m, AddTable(t, enc_k, v));
    }
}
procedure {:inline 2} $1_table_remove'address_u128'(m: $Mutation (Table int (int)), k: int)
returns (v: int, m': $Mutation(Table int (int))) {
    var enc_k: int;
    var t: Table int (int);
    enc_k := $EncodeKey'address'(k);
    t := $Dereference(m);
    if (!ContainsTable(t, enc_k)) {
        call $Abort($StdError(7/*INVALID_ARGUMENTS*/, 101/*ENOT_FOUND*/));
    } else {
        v := GetTable(t, enc_k);
        m' := $UpdateMutation(m, RemoveTable(t, enc_k));
    }
}
procedure {:inline 2} $1_table_borrow'address_u128'(t: Table int (int), k: int) returns (v: int) {
    var enc_k: int;
    enc_k := $EncodeKey'address'(k);
    if (!ContainsTable(t, enc_k)) {
        call $Abort($StdError(7/*INVALID_ARGUMENTS*/, 101/*ENOT_FOUND*/));
    } else {
        v := GetTable(t, $EncodeKey'address'(k));
    }
}
procedure {:inline 2} $1_table_borrow_mut'address_u128'(m: $Mutation (Table int (int)), k: int)
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
procedure {:inline 2} $1_table_borrow_mut_with_default'address_u128'(m: $Mutation (Table int (int)), k: int, default: int)
returns (dst: $Mutation (int), m': $Mutation (Table int (int))) {
    var enc_k: int;
    var t: Table int (int);
    var t': Table int (int);
    enc_k := $EncodeKey'address'(k);
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
function {:inline} $1_table_spec_contains'address_u128'(t: (Table int (int)), k: int): bool {
    ContainsTable(t, $EncodeKey'address'(k))
}
function {:inline} $1_table_spec_set'address_u128'(t: Table int (int), k: int, v: int): Table int (int) {
    (var enc_k := $EncodeKey'address'(k);
    if (ContainsTable(t, enc_k)) then
        UpdateTable(t, enc_k, v)
    else
        AddTable(t, enc_k, v))
}
function {:inline} $1_table_spec_remove'address_u128'(t: Table int (int), k: int): Table int (int) {
    RemoveTable(t, $EncodeKey'address'(k))
}
function {:inline} $1_table_spec_get'address_u128'(t: Table int (int), k: int): int {
    GetTable(t, $EncodeKey'address'(k))
}



// ----------------------------------------------------------------------------------
// Native Table implementation for type `(address,bv128)`

function $IsEqual'$1_table_Table'address_bv128''(t1: Table int (bv128), t2: Table int (bv128)): bool {
    LenTable(t1) == LenTable(t2) &&
    (forall k: int :: ContainsTable(t1, k) <==> ContainsTable(t2, k)) &&
    (forall k: int :: ContainsTable(t1, k) ==> GetTable(t1, k) == GetTable(t2, k)) &&
    (forall k: int :: ContainsTable(t2, k) ==> GetTable(t1, k) == GetTable(t2, k))
}

// Not inlined.
function $IsValid'$1_table_Table'address_bv128''(t: Table int (bv128)): bool {
    $IsValid'u64'(LenTable(t)) &&
    (forall i: int:: ContainsTable(t, i) ==> $IsValid'bv128'(GetTable(t, i)))
}
procedure {:inline 2} $1_table_new'address_bv128'() returns (v: Table int (bv128)) {
    v := EmptyTable();
}
procedure {:inline 2} $1_table_destroy'address_bv128'(t: Table int (bv128)) {
    if (LenTable(t) != 0) {
        call $Abort($StdError(1/*INVALID_STATE*/, 102/*ENOT_EMPTY*/));
    }
}
procedure {:inline 2} $1_table_contains'address_bv128'(t: (Table int (bv128)), k: int) returns (r: bool) {
    r := ContainsTable(t, $EncodeKey'address'(k));
}
procedure {:inline 2} $1_table_add'address_bv128'(m: $Mutation (Table int (bv128)), k: int, v: bv128) returns (m': $Mutation(Table int (bv128))) {
    var enc_k: int;
    var t: Table int (bv128);
    enc_k := $EncodeKey'address'(k);
    t := $Dereference(m);
    if (ContainsTable(t, enc_k)) {
        call $Abort($StdError(7/*INVALID_ARGUMENTS*/, 100/*EALREADY_EXISTS*/));
    } else {
        m' := $UpdateMutation(m, AddTable(t, enc_k, v));
    }
}
procedure {:inline 2} $1_table_upsert'address_bv128'(m: $Mutation (Table int (bv128)), k: int, v: bv128) returns (m': $Mutation(Table int (bv128))) {
    var enc_k: int;
    var t: Table int (bv128);
    enc_k := $EncodeKey'address'(k);
    t := $Dereference(m);
    if (ContainsTable(t, enc_k)) {
        m' := $UpdateMutation(m, UpdateTable(t, enc_k, v));
    } else {
        m' := $UpdateMutation(m, AddTable(t, enc_k, v));
    }
}
procedure {:inline 2} $1_table_remove'address_bv128'(m: $Mutation (Table int (bv128)), k: int)
returns (v: bv128, m': $Mutation(Table int (bv128))) {
    var enc_k: int;
    var t: Table int (bv128);
    enc_k := $EncodeKey'address'(k);
    t := $Dereference(m);
    if (!ContainsTable(t, enc_k)) {
        call $Abort($StdError(7/*INVALID_ARGUMENTS*/, 101/*ENOT_FOUND*/));
    } else {
        v := GetTable(t, enc_k);
        m' := $UpdateMutation(m, RemoveTable(t, enc_k));
    }
}
procedure {:inline 2} $1_table_borrow'address_bv128'(t: Table int (bv128), k: int) returns (v: bv128) {
    var enc_k: int;
    enc_k := $EncodeKey'address'(k);
    if (!ContainsTable(t, enc_k)) {
        call $Abort($StdError(7/*INVALID_ARGUMENTS*/, 101/*ENOT_FOUND*/));
    } else {
        v := GetTable(t, $EncodeKey'address'(k));
    }
}
procedure {:inline 2} $1_table_borrow_mut'address_bv128'(m: $Mutation (Table int (bv128)), k: int)
returns (dst: $Mutation (bv128), m': $Mutation (Table int (bv128))) {
    var enc_k: int;
    var t: Table int (bv128);
    enc_k := $EncodeKey'address'(k);
    t := $Dereference(m);
    if (!ContainsTable(t, enc_k)) {
        call $Abort($StdError(7/*INVALID_ARGUMENTS*/, 101/*ENOT_FOUND*/));
    } else {
        dst := $Mutation(l#$Mutation(m), ExtendVec(p#$Mutation(m), enc_k), GetTable(t, enc_k));
        m' := m;
    }
}
procedure {:inline 2} $1_table_borrow_mut_with_default'address_bv128'(m: $Mutation (Table int (bv128)), k: int, default: bv128)
returns (dst: $Mutation (bv128), m': $Mutation (Table int (bv128))) {
    var enc_k: int;
    var t: Table int (bv128);
    var t': Table int (bv128);
    enc_k := $EncodeKey'address'(k);
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
function {:inline} $1_table_spec_contains'address_bv128'(t: (Table int (bv128)), k: int): bool {
    ContainsTable(t, $EncodeKey'address'(k))
}
function {:inline} $1_table_spec_set'address_bv128'(t: Table int (bv128), k: int, v: bv128): Table int (bv128) {
    (var enc_k := $EncodeKey'address'(k);
    if (ContainsTable(t, enc_k)) then
        UpdateTable(t, enc_k, v)
    else
        AddTable(t, enc_k, v))
}
function {:inline} $1_table_spec_remove'address_bv128'(t: Table int (bv128), k: int): Table int (bv128) {
    RemoveTable(t, $EncodeKey'address'(k))
}
function {:inline} $1_table_spec_get'address_bv128'(t: Table int (bv128), k: int): bv128 {
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

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:14:9+116, instance <signer>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'signer'($1_from_bcs_deserialize'signer'(b1), $1_from_bcs_deserialize'signer'(b2)) ==> $IsEqual'vec'u8''(b1, b2))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:14:9+116, instance <vector<u8>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''($1_from_bcs_deserialize'vec'u8''(b1), $1_from_bcs_deserialize'vec'u8''(b2)) ==> $IsEqual'vec'u8''(b1, b2))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:14:9+116, instance <vector<u64>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u64''($1_from_bcs_deserialize'vec'u64''(b1), $1_from_bcs_deserialize'vec'u64''(b2)) ==> $IsEqual'vec'u8''(b1, b2))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:14:9+116, instance <vector<aggregator::Aggregator>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'$1_aggregator_Aggregator''($1_from_bcs_deserialize'vec'$1_aggregator_Aggregator''(b1), $1_from_bcs_deserialize'vec'$1_aggregator_Aggregator''(b2)) ==> $IsEqual'vec'u8''(b1, b2))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:14:9+116, instance <vector<optional_aggregator::Integer>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'$1_optional_aggregator_Integer''($1_from_bcs_deserialize'vec'$1_optional_aggregator_Integer''(b1), $1_from_bcs_deserialize'vec'$1_optional_aggregator_Integer''(b2)) ==> $IsEqual'vec'u8''(b1, b2))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:14:9+116, instance <vector<optional_aggregator::OptionalAggregator>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'$1_optional_aggregator_OptionalAggregator''($1_from_bcs_deserialize'vec'$1_optional_aggregator_OptionalAggregator''(b1), $1_from_bcs_deserialize'vec'$1_optional_aggregator_OptionalAggregator''(b2)) ==> $IsEqual'vec'u8''(b1, b2))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:14:9+116, instance <vector<aptos_coin::AptosCoin>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'$1_aptos_coin_AptosCoin''($1_from_bcs_deserialize'vec'$1_aptos_coin_AptosCoin''(b1), $1_from_bcs_deserialize'vec'$1_aptos_coin_AptosCoin''(b2)) ==> $IsEqual'vec'u8''(b1, b2))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:14:9+116, instance <vector<aptos_coin::DelegatedMintCapability>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'$1_aptos_coin_DelegatedMintCapability''($1_from_bcs_deserialize'vec'$1_aptos_coin_DelegatedMintCapability''(b1), $1_from_bcs_deserialize'vec'$1_aptos_coin_DelegatedMintCapability''(b2)) ==> $IsEqual'vec'u8''(b1, b2))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:14:9+116, instance <vector<#0>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'#0''($1_from_bcs_deserialize'vec'#0''(b1), $1_from_bcs_deserialize'vec'#0''(b2)) ==> $IsEqual'vec'u8''(b1, b2))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:14:9+116, instance <option::Option<u64>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'$1_option_Option'u64''($1_from_bcs_deserialize'$1_option_Option'u64''(b1), $1_from_bcs_deserialize'$1_option_Option'u64''(b2)) ==> $IsEqual'vec'u8''(b1, b2))));

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

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:14:9+116, instance <table::Table<address, u128>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'$1_table_Table'address_u128''($1_from_bcs_deserialize'$1_table_Table'address_u128''(b1), $1_from_bcs_deserialize'$1_table_Table'address_u128''(b2)) ==> $IsEqual'vec'u8''(b1, b2))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:14:9+116, instance <aggregator::Aggregator>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'$1_aggregator_Aggregator'($1_from_bcs_deserialize'$1_aggregator_Aggregator'(b1), $1_from_bcs_deserialize'$1_aggregator_Aggregator'(b2)) ==> $IsEqual'vec'u8''(b1, b2))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:14:9+116, instance <aggregator_factory::AggregatorFactory>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'$1_aggregator_factory_AggregatorFactory'($1_from_bcs_deserialize'$1_aggregator_factory_AggregatorFactory'(b1), $1_from_bcs_deserialize'$1_aggregator_factory_AggregatorFactory'(b2)) ==> $IsEqual'vec'u8''(b1, b2))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:14:9+116, instance <optional_aggregator::Integer>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'$1_optional_aggregator_Integer'($1_from_bcs_deserialize'$1_optional_aggregator_Integer'(b1), $1_from_bcs_deserialize'$1_optional_aggregator_Integer'(b2)) ==> $IsEqual'vec'u8''(b1, b2))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:14:9+116, instance <optional_aggregator::OptionalAggregator>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'$1_optional_aggregator_OptionalAggregator'($1_from_bcs_deserialize'$1_optional_aggregator_OptionalAggregator'(b1), $1_from_bcs_deserialize'$1_optional_aggregator_OptionalAggregator'(b2)) ==> $IsEqual'vec'u8''(b1, b2))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:14:9+116, instance <coin::BurnCapability<aptos_coin::AptosCoin>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'$1_coin_BurnCapability'$1_aptos_coin_AptosCoin''($1_from_bcs_deserialize'$1_coin_BurnCapability'$1_aptos_coin_AptosCoin''(b1), $1_from_bcs_deserialize'$1_coin_BurnCapability'$1_aptos_coin_AptosCoin''(b2)) ==> $IsEqual'vec'u8''(b1, b2))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:14:9+116, instance <coin::CoinInfo<aptos_coin::AptosCoin>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'$1_coin_CoinInfo'$1_aptos_coin_AptosCoin''($1_from_bcs_deserialize'$1_coin_CoinInfo'$1_aptos_coin_AptosCoin''(b1), $1_from_bcs_deserialize'$1_coin_CoinInfo'$1_aptos_coin_AptosCoin''(b2)) ==> $IsEqual'vec'u8''(b1, b2))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:14:9+116, instance <coin::FreezeCapability<aptos_coin::AptosCoin>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'$1_coin_FreezeCapability'$1_aptos_coin_AptosCoin''($1_from_bcs_deserialize'$1_coin_FreezeCapability'$1_aptos_coin_AptosCoin''(b1), $1_from_bcs_deserialize'$1_coin_FreezeCapability'$1_aptos_coin_AptosCoin''(b2)) ==> $IsEqual'vec'u8''(b1, b2))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:14:9+116, instance <coin::MintCapability<aptos_coin::AptosCoin>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'$1_coin_MintCapability'$1_aptos_coin_AptosCoin''($1_from_bcs_deserialize'$1_coin_MintCapability'$1_aptos_coin_AptosCoin''(b1), $1_from_bcs_deserialize'$1_coin_MintCapability'$1_aptos_coin_AptosCoin''(b2)) ==> $IsEqual'vec'u8''(b1, b2))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:14:9+116, instance <coin::Ghost$supply<aptos_coin::AptosCoin>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'$1_coin_Ghost$supply'$1_aptos_coin_AptosCoin''($1_from_bcs_deserialize'$1_coin_Ghost$supply'$1_aptos_coin_AptosCoin''(b1), $1_from_bcs_deserialize'$1_coin_Ghost$supply'$1_aptos_coin_AptosCoin''(b2)) ==> $IsEqual'vec'u8''(b1, b2))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:14:9+116, instance <coin::Ghost$aggregate_supply<aptos_coin::AptosCoin>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'$1_coin_Ghost$aggregate_supply'$1_aptos_coin_AptosCoin''($1_from_bcs_deserialize'$1_coin_Ghost$aggregate_supply'$1_aptos_coin_AptosCoin''(b1), $1_from_bcs_deserialize'$1_coin_Ghost$aggregate_supply'$1_aptos_coin_AptosCoin''(b2)) ==> $IsEqual'vec'u8''(b1, b2))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:14:9+116, instance <aptos_coin::AptosCoin>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'$1_aptos_coin_AptosCoin'($1_from_bcs_deserialize'$1_aptos_coin_AptosCoin'(b1), $1_from_bcs_deserialize'$1_aptos_coin_AptosCoin'(b2)) ==> $IsEqual'vec'u8''(b1, b2))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:14:9+116, instance <aptos_coin::DelegatedMintCapability>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'$1_aptos_coin_DelegatedMintCapability'($1_from_bcs_deserialize'$1_aptos_coin_DelegatedMintCapability'(b1), $1_from_bcs_deserialize'$1_aptos_coin_DelegatedMintCapability'(b2)) ==> $IsEqual'vec'u8''(b1, b2))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:14:9+116, instance <aptos_coin::Delegations>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'$1_aptos_coin_Delegations'($1_from_bcs_deserialize'$1_aptos_coin_Delegations'(b1), $1_from_bcs_deserialize'$1_aptos_coin_Delegations'(b2)) ==> $IsEqual'vec'u8''(b1, b2))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:14:9+116, instance <aptos_coin::MintCapStore>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'$1_aptos_coin_MintCapStore'($1_from_bcs_deserialize'$1_aptos_coin_MintCapStore'(b1), $1_from_bcs_deserialize'$1_aptos_coin_MintCapStore'(b2)) ==> $IsEqual'vec'u8''(b1, b2))));

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

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:18:9+124, instance <vector<aggregator::Aggregator>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'bool'($1_from_bcs_deserializable'vec'$1_aggregator_Aggregator''(b1), $1_from_bcs_deserializable'vec'$1_aggregator_Aggregator''(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:18:9+124, instance <vector<optional_aggregator::Integer>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'bool'($1_from_bcs_deserializable'vec'$1_optional_aggregator_Integer''(b1), $1_from_bcs_deserializable'vec'$1_optional_aggregator_Integer''(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:18:9+124, instance <vector<optional_aggregator::OptionalAggregator>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'bool'($1_from_bcs_deserializable'vec'$1_optional_aggregator_OptionalAggregator''(b1), $1_from_bcs_deserializable'vec'$1_optional_aggregator_OptionalAggregator''(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:18:9+124, instance <vector<aptos_coin::AptosCoin>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'bool'($1_from_bcs_deserializable'vec'$1_aptos_coin_AptosCoin''(b1), $1_from_bcs_deserializable'vec'$1_aptos_coin_AptosCoin''(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:18:9+124, instance <vector<aptos_coin::DelegatedMintCapability>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'bool'($1_from_bcs_deserializable'vec'$1_aptos_coin_DelegatedMintCapability''(b1), $1_from_bcs_deserializable'vec'$1_aptos_coin_DelegatedMintCapability''(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:18:9+124, instance <vector<#0>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'bool'($1_from_bcs_deserializable'vec'#0''(b1), $1_from_bcs_deserializable'vec'#0''(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:18:9+124, instance <option::Option<u64>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'bool'($1_from_bcs_deserializable'$1_option_Option'u64''(b1), $1_from_bcs_deserializable'$1_option_Option'u64''(b2)))));

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

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:18:9+124, instance <table::Table<address, u128>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'bool'($1_from_bcs_deserializable'$1_table_Table'address_u128''(b1), $1_from_bcs_deserializable'$1_table_Table'address_u128''(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:18:9+124, instance <aggregator::Aggregator>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'bool'($1_from_bcs_deserializable'$1_aggregator_Aggregator'(b1), $1_from_bcs_deserializable'$1_aggregator_Aggregator'(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:18:9+124, instance <aggregator_factory::AggregatorFactory>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'bool'($1_from_bcs_deserializable'$1_aggregator_factory_AggregatorFactory'(b1), $1_from_bcs_deserializable'$1_aggregator_factory_AggregatorFactory'(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:18:9+124, instance <optional_aggregator::Integer>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'bool'($1_from_bcs_deserializable'$1_optional_aggregator_Integer'(b1), $1_from_bcs_deserializable'$1_optional_aggregator_Integer'(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:18:9+124, instance <optional_aggregator::OptionalAggregator>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'bool'($1_from_bcs_deserializable'$1_optional_aggregator_OptionalAggregator'(b1), $1_from_bcs_deserializable'$1_optional_aggregator_OptionalAggregator'(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:18:9+124, instance <coin::BurnCapability<aptos_coin::AptosCoin>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'bool'($1_from_bcs_deserializable'$1_coin_BurnCapability'$1_aptos_coin_AptosCoin''(b1), $1_from_bcs_deserializable'$1_coin_BurnCapability'$1_aptos_coin_AptosCoin''(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:18:9+124, instance <coin::CoinInfo<aptos_coin::AptosCoin>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'bool'($1_from_bcs_deserializable'$1_coin_CoinInfo'$1_aptos_coin_AptosCoin''(b1), $1_from_bcs_deserializable'$1_coin_CoinInfo'$1_aptos_coin_AptosCoin''(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:18:9+124, instance <coin::FreezeCapability<aptos_coin::AptosCoin>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'bool'($1_from_bcs_deserializable'$1_coin_FreezeCapability'$1_aptos_coin_AptosCoin''(b1), $1_from_bcs_deserializable'$1_coin_FreezeCapability'$1_aptos_coin_AptosCoin''(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:18:9+124, instance <coin::MintCapability<aptos_coin::AptosCoin>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'bool'($1_from_bcs_deserializable'$1_coin_MintCapability'$1_aptos_coin_AptosCoin''(b1), $1_from_bcs_deserializable'$1_coin_MintCapability'$1_aptos_coin_AptosCoin''(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:18:9+124, instance <coin::Ghost$supply<aptos_coin::AptosCoin>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'bool'($1_from_bcs_deserializable'$1_coin_Ghost$supply'$1_aptos_coin_AptosCoin''(b1), $1_from_bcs_deserializable'$1_coin_Ghost$supply'$1_aptos_coin_AptosCoin''(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:18:9+124, instance <coin::Ghost$aggregate_supply<aptos_coin::AptosCoin>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'bool'($1_from_bcs_deserializable'$1_coin_Ghost$aggregate_supply'$1_aptos_coin_AptosCoin''(b1), $1_from_bcs_deserializable'$1_coin_Ghost$aggregate_supply'$1_aptos_coin_AptosCoin''(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:18:9+124, instance <aptos_coin::AptosCoin>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'bool'($1_from_bcs_deserializable'$1_aptos_coin_AptosCoin'(b1), $1_from_bcs_deserializable'$1_aptos_coin_AptosCoin'(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:18:9+124, instance <aptos_coin::DelegatedMintCapability>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'bool'($1_from_bcs_deserializable'$1_aptos_coin_DelegatedMintCapability'(b1), $1_from_bcs_deserializable'$1_aptos_coin_DelegatedMintCapability'(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:18:9+124, instance <aptos_coin::Delegations>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'bool'($1_from_bcs_deserializable'$1_aptos_coin_Delegations'(b1), $1_from_bcs_deserializable'$1_aptos_coin_Delegations'(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:18:9+124, instance <aptos_coin::MintCapStore>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'bool'($1_from_bcs_deserializable'$1_aptos_coin_MintCapStore'(b1), $1_from_bcs_deserializable'$1_aptos_coin_MintCapStore'(b2)))));

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

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:21:9+118, instance <vector<aggregator::Aggregator>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'vec'$1_aggregator_Aggregator''($1_from_bcs_deserialize'vec'$1_aggregator_Aggregator''(b1), $1_from_bcs_deserialize'vec'$1_aggregator_Aggregator''(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:21:9+118, instance <vector<optional_aggregator::Integer>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'vec'$1_optional_aggregator_Integer''($1_from_bcs_deserialize'vec'$1_optional_aggregator_Integer''(b1), $1_from_bcs_deserialize'vec'$1_optional_aggregator_Integer''(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:21:9+118, instance <vector<optional_aggregator::OptionalAggregator>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'vec'$1_optional_aggregator_OptionalAggregator''($1_from_bcs_deserialize'vec'$1_optional_aggregator_OptionalAggregator''(b1), $1_from_bcs_deserialize'vec'$1_optional_aggregator_OptionalAggregator''(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:21:9+118, instance <vector<aptos_coin::AptosCoin>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'vec'$1_aptos_coin_AptosCoin''($1_from_bcs_deserialize'vec'$1_aptos_coin_AptosCoin''(b1), $1_from_bcs_deserialize'vec'$1_aptos_coin_AptosCoin''(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:21:9+118, instance <vector<aptos_coin::DelegatedMintCapability>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'vec'$1_aptos_coin_DelegatedMintCapability''($1_from_bcs_deserialize'vec'$1_aptos_coin_DelegatedMintCapability''(b1), $1_from_bcs_deserialize'vec'$1_aptos_coin_DelegatedMintCapability''(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:21:9+118, instance <vector<#0>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'vec'#0''($1_from_bcs_deserialize'vec'#0''(b1), $1_from_bcs_deserialize'vec'#0''(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:21:9+118, instance <option::Option<u64>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'$1_option_Option'u64''($1_from_bcs_deserialize'$1_option_Option'u64''(b1), $1_from_bcs_deserialize'$1_option_Option'u64''(b2)))));

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

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:21:9+118, instance <table::Table<address, u128>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'$1_table_Table'address_u128''($1_from_bcs_deserialize'$1_table_Table'address_u128''(b1), $1_from_bcs_deserialize'$1_table_Table'address_u128''(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:21:9+118, instance <aggregator::Aggregator>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'$1_aggregator_Aggregator'($1_from_bcs_deserialize'$1_aggregator_Aggregator'(b1), $1_from_bcs_deserialize'$1_aggregator_Aggregator'(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:21:9+118, instance <aggregator_factory::AggregatorFactory>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'$1_aggregator_factory_AggregatorFactory'($1_from_bcs_deserialize'$1_aggregator_factory_AggregatorFactory'(b1), $1_from_bcs_deserialize'$1_aggregator_factory_AggregatorFactory'(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:21:9+118, instance <optional_aggregator::Integer>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'$1_optional_aggregator_Integer'($1_from_bcs_deserialize'$1_optional_aggregator_Integer'(b1), $1_from_bcs_deserialize'$1_optional_aggregator_Integer'(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:21:9+118, instance <optional_aggregator::OptionalAggregator>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'$1_optional_aggregator_OptionalAggregator'($1_from_bcs_deserialize'$1_optional_aggregator_OptionalAggregator'(b1), $1_from_bcs_deserialize'$1_optional_aggregator_OptionalAggregator'(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:21:9+118, instance <coin::BurnCapability<aptos_coin::AptosCoin>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'$1_coin_BurnCapability'$1_aptos_coin_AptosCoin''($1_from_bcs_deserialize'$1_coin_BurnCapability'$1_aptos_coin_AptosCoin''(b1), $1_from_bcs_deserialize'$1_coin_BurnCapability'$1_aptos_coin_AptosCoin''(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:21:9+118, instance <coin::CoinInfo<aptos_coin::AptosCoin>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'$1_coin_CoinInfo'$1_aptos_coin_AptosCoin''($1_from_bcs_deserialize'$1_coin_CoinInfo'$1_aptos_coin_AptosCoin''(b1), $1_from_bcs_deserialize'$1_coin_CoinInfo'$1_aptos_coin_AptosCoin''(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:21:9+118, instance <coin::FreezeCapability<aptos_coin::AptosCoin>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'$1_coin_FreezeCapability'$1_aptos_coin_AptosCoin''($1_from_bcs_deserialize'$1_coin_FreezeCapability'$1_aptos_coin_AptosCoin''(b1), $1_from_bcs_deserialize'$1_coin_FreezeCapability'$1_aptos_coin_AptosCoin''(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:21:9+118, instance <coin::MintCapability<aptos_coin::AptosCoin>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'$1_coin_MintCapability'$1_aptos_coin_AptosCoin''($1_from_bcs_deserialize'$1_coin_MintCapability'$1_aptos_coin_AptosCoin''(b1), $1_from_bcs_deserialize'$1_coin_MintCapability'$1_aptos_coin_AptosCoin''(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:21:9+118, instance <coin::Ghost$supply<aptos_coin::AptosCoin>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'$1_coin_Ghost$supply'$1_aptos_coin_AptosCoin''($1_from_bcs_deserialize'$1_coin_Ghost$supply'$1_aptos_coin_AptosCoin''(b1), $1_from_bcs_deserialize'$1_coin_Ghost$supply'$1_aptos_coin_AptosCoin''(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:21:9+118, instance <coin::Ghost$aggregate_supply<aptos_coin::AptosCoin>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'$1_coin_Ghost$aggregate_supply'$1_aptos_coin_AptosCoin''($1_from_bcs_deserialize'$1_coin_Ghost$aggregate_supply'$1_aptos_coin_AptosCoin''(b1), $1_from_bcs_deserialize'$1_coin_Ghost$aggregate_supply'$1_aptos_coin_AptosCoin''(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:21:9+118, instance <aptos_coin::AptosCoin>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'$1_aptos_coin_AptosCoin'($1_from_bcs_deserialize'$1_aptos_coin_AptosCoin'(b1), $1_from_bcs_deserialize'$1_aptos_coin_AptosCoin'(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:21:9+118, instance <aptos_coin::DelegatedMintCapability>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'$1_aptos_coin_DelegatedMintCapability'($1_from_bcs_deserialize'$1_aptos_coin_DelegatedMintCapability'(b1), $1_from_bcs_deserialize'$1_aptos_coin_DelegatedMintCapability'(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:21:9+118, instance <aptos_coin::Delegations>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'$1_aptos_coin_Delegations'($1_from_bcs_deserialize'$1_aptos_coin_Delegations'(b1), $1_from_bcs_deserialize'$1_aptos_coin_Delegations'(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:21:9+118, instance <aptos_coin::MintCapStore>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'$1_aptos_coin_MintCapStore'($1_from_bcs_deserialize'$1_aptos_coin_MintCapStore'(b1), $1_from_bcs_deserialize'$1_aptos_coin_MintCapStore'(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:21:9+118, instance <#0>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'#0'($1_from_bcs_deserialize'#0'(b1), $1_from_bcs_deserialize'#0'(b2)))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/hash.spec.move:8:9+113
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''($1_aptos_hash_spec_keccak256(b1), $1_aptos_hash_spec_keccak256(b2)) ==> $IsEqual'vec'u8''(b1, b2))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/hash.spec.move:13:9+129
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''($1_aptos_hash_spec_sha2_512_internal(b1), $1_aptos_hash_spec_sha2_512_internal(b2)) ==> $IsEqual'vec'u8''(b1, b2))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/hash.spec.move:18:9+129
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''($1_aptos_hash_spec_sha3_512_internal(b1), $1_aptos_hash_spec_sha3_512_internal(b2)) ==> $IsEqual'vec'u8''(b1, b2))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/hash.spec.move:23:9+131
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''($1_aptos_hash_spec_ripemd160_internal(b1), $1_aptos_hash_spec_ripemd160_internal(b2)) ==> $IsEqual'vec'u8''(b1, b2))));

// axiom at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/hash.spec.move:28:9+135
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''($1_aptos_hash_spec_blake2b_256_internal(b1), $1_aptos_hash_spec_blake2b_256_internal(b2)) ==> $IsEqual'vec'u8''(b1, b2))));

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/../move-stdlib/sources/vector.move:146:5+86
function {:inline} $1_vector_$is_empty'u64'(v: Vec (int)): bool {
    $IsEqual'u64'($1_vector_$length'u64'(v), 0)
}

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/../move-stdlib/sources/vector.move:146:5+86
function {:inline} $1_vector_$is_empty'$1_aggregator_Aggregator'(v: Vec ($1_aggregator_Aggregator)): bool {
    $IsEqual'u64'($1_vector_$length'$1_aggregator_Aggregator'(v), 0)
}

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/../move-stdlib/sources/vector.move:146:5+86
function {:inline} $1_vector_$is_empty'$1_optional_aggregator_Integer'(v: Vec ($1_optional_aggregator_Integer)): bool {
    $IsEqual'u64'($1_vector_$length'$1_optional_aggregator_Integer'(v), 0)
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

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/../move-stdlib/sources/option.move:34:10+78
function {:inline} $1_option_spec_none'u64'(): $1_option_Option'u64' {
    $1_option_Option'u64'($EmptyVec'u64'())
}

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/../move-stdlib/sources/option.move:34:10+78
function {:inline} $1_option_spec_none'$1_aggregator_Aggregator'(): $1_option_Option'$1_aggregator_Aggregator' {
    $1_option_Option'$1_aggregator_Aggregator'($EmptyVec'$1_aggregator_Aggregator'())
}

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/../move-stdlib/sources/option.move:34:10+78
function {:inline} $1_option_spec_none'$1_optional_aggregator_Integer'(): $1_option_Option'$1_optional_aggregator_Integer' {
    $1_option_Option'$1_optional_aggregator_Integer'($EmptyVec'$1_optional_aggregator_Integer'())
}

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/../move-stdlib/sources/option.move:34:10+78
function {:inline} $1_option_spec_none'$1_optional_aggregator_OptionalAggregator'(): $1_option_Option'$1_optional_aggregator_OptionalAggregator' {
    $1_option_Option'$1_optional_aggregator_OptionalAggregator'($EmptyVec'$1_optional_aggregator_OptionalAggregator'())
}

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/../move-stdlib/sources/option.move:47:10+89
function {:inline} $1_option_spec_some'u64'(e: int): $1_option_Option'u64' {
    $1_option_Option'u64'(MakeVec1(e))
}

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/../move-stdlib/sources/option.move:47:10+89
function {:inline} $1_option_spec_some'$1_aggregator_Aggregator'(e: $1_aggregator_Aggregator): $1_option_Option'$1_aggregator_Aggregator' {
    $1_option_Option'$1_aggregator_Aggregator'(MakeVec1(e))
}

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/../move-stdlib/sources/option.move:47:10+89
function {:inline} $1_option_spec_some'$1_optional_aggregator_Integer'(e: $1_optional_aggregator_Integer): $1_option_Option'$1_optional_aggregator_Integer' {
    $1_option_Option'$1_optional_aggregator_Integer'(MakeVec1(e))
}

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/../move-stdlib/sources/option.move:47:10+89
function {:inline} $1_option_spec_some'$1_optional_aggregator_OptionalAggregator'(e: $1_optional_aggregator_OptionalAggregator): $1_option_Option'$1_optional_aggregator_OptionalAggregator' {
    $1_option_Option'$1_optional_aggregator_OptionalAggregator'(MakeVec1(e))
}

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/../move-stdlib/sources/option.move:69:10+91
function {:inline} $1_option_spec_is_none'u64'(t: $1_option_Option'u64'): bool {
    $1_vector_$is_empty'u64'($vec#$1_option_Option'u64'(t))
}

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/../move-stdlib/sources/option.move:111:10+78
function {:inline} $1_option_spec_borrow'u64'(t: $1_option_Option'u64'): int {
    ReadVec($vec#$1_option_Option'u64'(t), 0)
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

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/../move-stdlib/sources/signer.move:12:5+77
function {:inline} $1_signer_$address_of(s: $signer): int {
    $1_signer_$borrow_address(s)
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

// fun error::already_exists [baseline] at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/../move-stdlib/sources/error.move:83:3+71
procedure {:inline 1} $1_error_already_exists(_$t0: int) returns ($ret0: int)
{
    // declare local variables
    var $t1: int;
    var $t2: int;
    var $t3: int;
    var $t0: int;
    var $temp_0'u64': int;
    $t0 := _$t0;

    // bytecode translation starts here
    // trace_local[r]($t0) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/../move-stdlib/sources/error.move:83:3+1
    assume {:print "$at(10,3585,3586)"} true;
    assume {:print "$track_local(4,1,0):", $t0} $t0 == $t0;

    // $t1 := 8 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/../move-stdlib/sources/error.move:83:54+14
    $t1 := 8;
    assume $IsValid'u64'($t1);

    // assume Identical($t2, Shl($t1, 16)) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/../move-stdlib/sources/error.move:69:5+29
    assume {:print "$at(10,2844,2873)"} true;
    assume ($t2 == $shlU64($t1, 16));

    // $t3 := opaque begin: error::canonical($t1, $t0) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/../move-stdlib/sources/error.move:83:44+28
    assume {:print "$at(10,3626,3654)"} true;

    // assume WellFormed($t3) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/../move-stdlib/sources/error.move:83:44+28
    assume $IsValid'u64'($t3);

    // assume Eq<u64>($t3, $t1) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/../move-stdlib/sources/error.move:83:44+28
    assume $IsEqual'u64'($t3, $t1);

    // $t3 := opaque end: error::canonical($t1, $t0) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/../move-stdlib/sources/error.move:83:44+28

    // trace_return[0]($t3) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/../move-stdlib/sources/error.move:83:44+28
    assume {:print "$track_return(4,1,0):", $t3} $t3 == $t3;

    // label L1 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/../move-stdlib/sources/error.move:83:73+1
L1:

    // return $t3 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/../move-stdlib/sources/error.move:83:73+1
    assume {:print "$at(10,3655,3656)"} true;
    $ret0 := $t3;
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
function  $1_from_bcs_deserialize'vec'$1_aptos_coin_DelegatedMintCapability''(bytes: Vec (int)): Vec ($1_aptos_coin_DelegatedMintCapability);
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserialize'vec'$1_aptos_coin_DelegatedMintCapability''(bytes);
$IsValid'vec'$1_aptos_coin_DelegatedMintCapability''($$res)));

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
function  $1_from_bcs_deserialize'$1_table_Table'address_u128''(bytes: Vec (int)): Table int (int);
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserialize'$1_table_Table'address_u128''(bytes);
$IsValid'$1_table_Table'address_u128''($$res)));

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:7:9+41
function  $1_from_bcs_deserialize'$1_aggregator_Aggregator'(bytes: Vec (int)): $1_aggregator_Aggregator;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserialize'$1_aggregator_Aggregator'(bytes);
$IsValid'$1_aggregator_Aggregator'($$res)));

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:7:9+41
function  $1_from_bcs_deserialize'$1_aggregator_factory_AggregatorFactory'(bytes: Vec (int)): $1_aggregator_factory_AggregatorFactory;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserialize'$1_aggregator_factory_AggregatorFactory'(bytes);
$IsValid'$1_aggregator_factory_AggregatorFactory'($$res)));

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
function  $1_from_bcs_deserialize'$1_coin_CoinInfo'$1_aptos_coin_AptosCoin''(bytes: Vec (int)): $1_coin_CoinInfo'$1_aptos_coin_AptosCoin';
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserialize'$1_coin_CoinInfo'$1_aptos_coin_AptosCoin''(bytes);
$IsValid'$1_coin_CoinInfo'$1_aptos_coin_AptosCoin''($$res)));

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:7:9+41
function  $1_from_bcs_deserialize'$1_coin_FreezeCapability'$1_aptos_coin_AptosCoin''(bytes: Vec (int)): $1_coin_FreezeCapability'$1_aptos_coin_AptosCoin';
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserialize'$1_coin_FreezeCapability'$1_aptos_coin_AptosCoin''(bytes);
$IsValid'$1_coin_FreezeCapability'$1_aptos_coin_AptosCoin''($$res)));

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:7:9+41
function  $1_from_bcs_deserialize'$1_coin_MintCapability'$1_aptos_coin_AptosCoin''(bytes: Vec (int)): $1_coin_MintCapability'$1_aptos_coin_AptosCoin';
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserialize'$1_coin_MintCapability'$1_aptos_coin_AptosCoin''(bytes);
$IsValid'$1_coin_MintCapability'$1_aptos_coin_AptosCoin''($$res)));

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
function  $1_from_bcs_deserialize'$1_aptos_coin_DelegatedMintCapability'(bytes: Vec (int)): $1_aptos_coin_DelegatedMintCapability;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserialize'$1_aptos_coin_DelegatedMintCapability'(bytes);
$IsValid'$1_aptos_coin_DelegatedMintCapability'($$res)));

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:7:9+41
function  $1_from_bcs_deserialize'$1_aptos_coin_Delegations'(bytes: Vec (int)): $1_aptos_coin_Delegations;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserialize'$1_aptos_coin_Delegations'(bytes);
$IsValid'$1_aptos_coin_Delegations'($$res)));

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:7:9+41
function  $1_from_bcs_deserialize'$1_aptos_coin_MintCapStore'(bytes: Vec (int)): $1_aptos_coin_MintCapStore;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserialize'$1_aptos_coin_MintCapStore'(bytes);
$IsValid'$1_aptos_coin_MintCapStore'($$res)));

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
function  $1_from_bcs_deserializable'vec'$1_aptos_coin_DelegatedMintCapability''(bytes: Vec (int)): bool;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserializable'vec'$1_aptos_coin_DelegatedMintCapability''(bytes);
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
function  $1_from_bcs_deserializable'$1_table_Table'address_u128''(bytes: Vec (int)): bool;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserializable'$1_table_Table'address_u128''(bytes);
$IsValid'bool'($$res)));

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:11:9+47
function  $1_from_bcs_deserializable'$1_aggregator_Aggregator'(bytes: Vec (int)): bool;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserializable'$1_aggregator_Aggregator'(bytes);
$IsValid'bool'($$res)));

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:11:9+47
function  $1_from_bcs_deserializable'$1_aggregator_factory_AggregatorFactory'(bytes: Vec (int)): bool;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserializable'$1_aggregator_factory_AggregatorFactory'(bytes);
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
function  $1_from_bcs_deserializable'$1_coin_CoinInfo'$1_aptos_coin_AptosCoin''(bytes: Vec (int)): bool;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserializable'$1_coin_CoinInfo'$1_aptos_coin_AptosCoin''(bytes);
$IsValid'bool'($$res)));

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:11:9+47
function  $1_from_bcs_deserializable'$1_coin_FreezeCapability'$1_aptos_coin_AptosCoin''(bytes: Vec (int)): bool;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserializable'$1_coin_FreezeCapability'$1_aptos_coin_AptosCoin''(bytes);
$IsValid'bool'($$res)));

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:11:9+47
function  $1_from_bcs_deserializable'$1_coin_MintCapability'$1_aptos_coin_AptosCoin''(bytes: Vec (int)): bool;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserializable'$1_coin_MintCapability'$1_aptos_coin_AptosCoin''(bytes);
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
function  $1_from_bcs_deserializable'$1_aptos_coin_DelegatedMintCapability'(bytes: Vec (int)): bool;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserializable'$1_aptos_coin_DelegatedMintCapability'(bytes);
$IsValid'bool'($$res)));

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:11:9+47
function  $1_from_bcs_deserializable'$1_aptos_coin_Delegations'(bytes: Vec (int)): bool;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserializable'$1_aptos_coin_Delegations'(bytes);
$IsValid'bool'($$res)));

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:11:9+47
function  $1_from_bcs_deserializable'$1_aptos_coin_MintCapStore'(bytes: Vec (int)): bool;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserializable'$1_aptos_coin_MintCapStore'(bytes);
$IsValid'bool'($$res)));

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/from_bcs.spec.move:11:9+47
function  $1_from_bcs_deserializable'#0'(bytes: Vec (int)): bool;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserializable'#0'(bytes);
$IsValid'bool'($$res)));

// struct aggregator_factory::AggregatorFactory at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aggregator/aggregator_factory.move:22:5+85
type {:datatype} $1_aggregator_factory_AggregatorFactory;
function {:constructor} $1_aggregator_factory_AggregatorFactory($phantom_table: Table int (int)): $1_aggregator_factory_AggregatorFactory;
function {:inline} $Update'$1_aggregator_factory_AggregatorFactory'_phantom_table(s: $1_aggregator_factory_AggregatorFactory, x: Table int (int)): $1_aggregator_factory_AggregatorFactory {
    $1_aggregator_factory_AggregatorFactory(x)
}
function $IsValid'$1_aggregator_factory_AggregatorFactory'(s: $1_aggregator_factory_AggregatorFactory): bool {
    $IsValid'$1_table_Table'address_u128''($phantom_table#$1_aggregator_factory_AggregatorFactory(s))
}
function {:inline} $IsEqual'$1_aggregator_factory_AggregatorFactory'(s1: $1_aggregator_factory_AggregatorFactory, s2: $1_aggregator_factory_AggregatorFactory): bool {
    s1 == s2
}
var $1_aggregator_factory_AggregatorFactory_$memory: $Memory $1_aggregator_factory_AggregatorFactory;

// fun aggregator_factory::create_aggregator_internal [baseline] at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aggregator/aggregator_factory.move:36:5+390
procedure {:inline 1} $1_aggregator_factory_create_aggregator_internal(_$t0: int) returns ($ret0: $1_aggregator_Aggregator)
{
    // declare local variables
    var $t1: int;
    var $t2: bool;
    var $t3: int;
    var $t4: int;
    var $t5: int;
    var $t6: int;
    var $t7: $Mutation ($1_aggregator_factory_AggregatorFactory);
    var $t8: $1_aggregator_Aggregator;
    var $t0: int;
    var $temp_0'$1_aggregator_Aggregator': $1_aggregator_Aggregator;
    var $temp_0'$1_aggregator_factory_AggregatorFactory': $1_aggregator_factory_AggregatorFactory;
    var $temp_0'u128': int;
    $t0 := _$t0;

    // bytecode translation starts here
    // trace_local[limit]($t0) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aggregator/aggregator_factory.move:36:5+1
    assume {:print "$at(77,1467,1468)"} true;
    assume {:print "$track_local(20,1,0):", $t0} $t0 == $t0;

    // $t1 := 0x1 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aggregator/aggregator_factory.move:38:39+16
    assume {:print "$at(77,1622,1638)"} true;
    $t1 := 1;
    assume $IsValid'address'($t1);

    // $t2 := exists<aggregator_factory::AggregatorFactory>($t1) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aggregator/aggregator_factory.move:38:13+6
    $t2 := $ResourceExists($1_aggregator_factory_AggregatorFactory_$memory, $t1);

    // if ($t2) goto L1 else goto L0 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aggregator/aggregator_factory.move:37:9+135
    assume {:print "$at(77,1575,1710)"} true;
    if ($t2) { goto L1; } else { goto L0; }

    // label L1 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aggregator/aggregator_factory.move:37:9+135
L1:

    // goto L2 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aggregator/aggregator_factory.move:37:9+135
    assume {:print "$at(77,1575,1710)"} true;
    goto L2;

    // label L0 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aggregator/aggregator_factory.move:39:30+29
    assume {:print "$at(77,1670,1699)"} true;
L0:

    // $t3 := 1 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aggregator/aggregator_factory.move:39:30+29
    assume {:print "$at(77,1670,1699)"} true;
    $t3 := 1;
    assume $IsValid'u64'($t3);

    // $t4 := error::not_found($t3) on_abort goto L4 with $t5 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aggregator/aggregator_factory.move:39:13+47
    call $t4 := $1_error_not_found($t3);
    if ($abort_flag) {
        assume {:print "$at(77,1653,1700)"} true;
        $t5 := $abort_code;
        assume {:print "$track_abort(20,1):", $t5} $t5 == $t5;
        goto L4;
    }

    // trace_abort($t4) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aggregator/aggregator_factory.move:37:9+135
    assume {:print "$at(77,1575,1710)"} true;
    assume {:print "$track_abort(20,1):", $t4} $t4 == $t4;

    // $t5 := move($t4) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aggregator/aggregator_factory.move:37:9+135
    $t5 := $t4;

    // goto L4 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aggregator/aggregator_factory.move:37:9+135
    goto L4;

    // label L2 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aggregator/aggregator_factory.move:42:71+16
    assume {:print "$at(77,1783,1799)"} true;
L2:

    // $t6 := 0x1 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aggregator/aggregator_factory.move:42:71+16
    assume {:print "$at(77,1783,1799)"} true;
    $t6 := 1;
    assume $IsValid'address'($t6);

    // $t7 := borrow_global<aggregator_factory::AggregatorFactory>($t6) on_abort goto L4 with $t5 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aggregator/aggregator_factory.move:42:34+17
    if (!$ResourceExists($1_aggregator_factory_AggregatorFactory_$memory, $t6)) {
        call $ExecFailureAbort();
    } else {
        $t7 := $Mutation($Global($t6), EmptyVec(), $ResourceValue($1_aggregator_factory_AggregatorFactory_$memory, $t6));
    }
    if ($abort_flag) {
        assume {:print "$at(77,1746,1763)"} true;
        $t5 := $abort_code;
        assume {:print "$track_abort(20,1):", $t5} $t5 == $t5;
        goto L4;
    }

    // $t8 := opaque begin: aggregator_factory::new_aggregator($t7, $t0) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aggregator/aggregator_factory.move:43:9+41
    assume {:print "$at(77,1810,1851)"} true;

    // $t7 := havoc[mut]() at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aggregator/aggregator_factory.move:43:9+41
    havoc $temp_0'$1_aggregator_factory_AggregatorFactory';
    $t7 := $UpdateMutation($t7, $temp_0'$1_aggregator_factory_AggregatorFactory');

    // assume WellFormed($t7) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aggregator/aggregator_factory.move:43:9+41
    assume $IsValid'$1_aggregator_factory_AggregatorFactory'($Dereference($t7));

    // assume WellFormed($t8) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aggregator/aggregator_factory.move:43:9+41
    assume $IsValid'$1_aggregator_Aggregator'($t8);

    // assume Eq<aggregator::Aggregator>($t8, aggregator_factory::spec_new_aggregator($t0)) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aggregator/aggregator_factory.move:43:9+41
    assume $IsEqual'$1_aggregator_Aggregator'($t8, $1_aggregator_factory_spec_new_aggregator($t0));

    // assume Eq<u128>(aggregator::spec_get_limit($t8), $t0) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aggregator/aggregator_factory.move:43:9+41
    assume $IsEqual'u128'($1_aggregator_spec_get_limit($t8), $t0);

    // $t8 := opaque end: aggregator_factory::new_aggregator($t7, $t0) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aggregator/aggregator_factory.move:43:9+41

    // write_back[aggregator_factory::AggregatorFactory@]($t7) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aggregator/aggregator_factory.move:43:9+41
    $1_aggregator_factory_AggregatorFactory_$memory := $ResourceUpdate($1_aggregator_factory_AggregatorFactory_$memory, $GlobalLocationAddress($t7),
        $Dereference($t7));

    // trace_return[0]($t8) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aggregator/aggregator_factory.move:43:9+41
    assume {:print "$track_return(20,1,0):", $t8} $t8 == $t8;

    // label L3 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aggregator/aggregator_factory.move:44:5+1
    assume {:print "$at(77,1856,1857)"} true;
L3:

    // return $t8 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aggregator/aggregator_factory.move:44:5+1
    assume {:print "$at(77,1856,1857)"} true;
    $ret0 := $t8;
    return;

    // label L4 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aggregator/aggregator_factory.move:44:5+1
L4:

    // abort($t5) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aggregator/aggregator_factory.move:44:5+1
    assume {:print "$at(77,1856,1857)"} true;
    $abort_code := $t5;
    $abort_flag := true;
    return;

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

// fun optional_aggregator::new [baseline] at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aggregator/optional_aggregator.move:72:5+477
procedure {:inline 1} $1_optional_aggregator_new(_$t0: int, _$t1: bool) returns ($ret0: $1_optional_aggregator_OptionalAggregator)
{
    // declare local variables
    var $t2: $1_optional_aggregator_OptionalAggregator;
    var $t3: $1_aggregator_Aggregator;
    var $t4: int;
    var $t5: $1_option_Option'$1_aggregator_Aggregator';
    var $t6: $1_option_Option'$1_optional_aggregator_Integer';
    var $t7: $1_option_Option'$1_aggregator_Aggregator';
    var $t8: $1_optional_aggregator_Integer;
    var $t9: $1_option_Option'$1_optional_aggregator_Integer';
    var $t0: int;
    var $t1: bool;
    var $temp_0'$1_optional_aggregator_OptionalAggregator': $1_optional_aggregator_OptionalAggregator;
    var $temp_0'bool': bool;
    var $temp_0'u128': int;
    $t0 := _$t0;
    $t1 := _$t1;

    // bytecode translation starts here
    // trace_local[limit]($t0) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aggregator/optional_aggregator.move:72:5+1
    assume {:print "$at(79,2306,2307)"} true;
    assume {:print "$track_local(22,8,0):", $t0} $t0 == $t0;

    // trace_local[parallelizable]($t1) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aggregator/optional_aggregator.move:72:5+1
    assume {:print "$track_local(22,8,1):", $t1} $t1 == $t1;

    // if ($t1) goto L1 else goto L0 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aggregator/optional_aggregator.move:73:9+383
    assume {:print "$at(79,2394,2777)"} true;
    if ($t1) { goto L1; } else { goto L0; }

    // label L1 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aggregator/optional_aggregator.move:75:89+5
    assume {:print "$at(79,2537,2542)"} true;
L1:

    // $t3 := aggregator_factory::create_aggregator_internal($t0) on_abort goto L4 with $t4 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aggregator/optional_aggregator.move:75:42+53
    assume {:print "$at(79,2490,2543)"} true;
    call $t3 := $1_aggregator_factory_create_aggregator_internal($t0);
    if ($abort_flag) {
        assume {:print "$at(79,2490,2543)"} true;
        $t4 := $abort_code;
        assume {:print "$track_abort(22,8):", $t4} $t4 == $t4;
        goto L4;
    }

    // $t5 := opaque begin: option::some<aggregator::Aggregator>($t3) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aggregator/optional_aggregator.move:75:29+67

    // assume And(WellFormed($t5), Le(Len<aggregator::Aggregator>(select option::Option.vec($t5)), 1)) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aggregator/optional_aggregator.move:75:29+67
    assume ($IsValid'$1_option_Option'$1_aggregator_Aggregator''($t5) && (LenVec($vec#$1_option_Option'$1_aggregator_Aggregator'($t5)) <= 1));

    // assume Eq<option::Option<aggregator::Aggregator>>($t5, option::spec_some<aggregator::Aggregator>($t3)) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aggregator/optional_aggregator.move:75:29+67
    assume $IsEqual'$1_option_Option'$1_aggregator_Aggregator''($t5, $1_option_spec_some'$1_aggregator_Aggregator'($t3));

    // $t5 := opaque end: option::some<aggregator::Aggregator>($t3) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aggregator/optional_aggregator.move:75:29+67

    // $t6 := opaque begin: option::none<optional_aggregator::Integer>() at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aggregator/optional_aggregator.move:76:26+14
    assume {:print "$at(79,2571,2585)"} true;

    // assume And(WellFormed($t6), Le(Len<optional_aggregator::Integer>(select option::Option.vec($t6)), 1)) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aggregator/optional_aggregator.move:76:26+14
    assume ($IsValid'$1_option_Option'$1_optional_aggregator_Integer''($t6) && (LenVec($vec#$1_option_Option'$1_optional_aggregator_Integer'($t6)) <= 1));

    // assume Eq<option::Option<optional_aggregator::Integer>>($t6, option::spec_none<optional_aggregator::Integer>()) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aggregator/optional_aggregator.move:76:26+14
    assume $IsEqual'$1_option_Option'$1_optional_aggregator_Integer''($t6, $1_option_spec_none'$1_optional_aggregator_Integer'());

    // $t6 := opaque end: option::none<optional_aggregator::Integer>() at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aggregator/optional_aggregator.move:76:26+14

    // $t2 := pack optional_aggregator::OptionalAggregator($t5, $t6) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aggregator/optional_aggregator.move:74:13+172
    assume {:print "$at(79,2428,2600)"} true;
    $t2 := $1_optional_aggregator_OptionalAggregator($t5, $t6);

    // goto L2 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aggregator/optional_aggregator.move:73:9+383
    assume {:print "$at(79,2394,2777)"} true;
    goto L2;

    // label L0 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aggregator/optional_aggregator.move:80:29+14
    assume {:print "$at(79,2679,2693)"} true;
L0:

    // $t7 := opaque begin: option::none<aggregator::Aggregator>() at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aggregator/optional_aggregator.move:80:29+14
    assume {:print "$at(79,2679,2693)"} true;

    // assume And(WellFormed($t7), Le(Len<aggregator::Aggregator>(select option::Option.vec($t7)), 1)) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aggregator/optional_aggregator.move:80:29+14
    assume ($IsValid'$1_option_Option'$1_aggregator_Aggregator''($t7) && (LenVec($vec#$1_option_Option'$1_aggregator_Aggregator'($t7)) <= 1));

    // assume Eq<option::Option<aggregator::Aggregator>>($t7, option::spec_none<aggregator::Aggregator>()) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aggregator/optional_aggregator.move:80:29+14
    assume $IsEqual'$1_option_Option'$1_aggregator_Aggregator''($t7, $1_option_spec_none'$1_aggregator_Aggregator'());

    // $t7 := opaque end: option::none<aggregator::Aggregator>() at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aggregator/optional_aggregator.move:80:29+14

    // $t8 := optional_aggregator::new_integer($t0) on_abort goto L4 with $t4 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aggregator/optional_aggregator.move:81:39+18
    assume {:print "$at(79,2733,2751)"} true;
    call $t8 := $1_optional_aggregator_new_integer($t0);
    if ($abort_flag) {
        assume {:print "$at(79,2733,2751)"} true;
        $t4 := $abort_code;
        assume {:print "$track_abort(22,8):", $t4} $t4 == $t4;
        goto L4;
    }

    // $t9 := opaque begin: option::some<optional_aggregator::Integer>($t8) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aggregator/optional_aggregator.move:81:26+32

    // assume And(WellFormed($t9), Le(Len<optional_aggregator::Integer>(select option::Option.vec($t9)), 1)) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aggregator/optional_aggregator.move:81:26+32
    assume ($IsValid'$1_option_Option'$1_optional_aggregator_Integer''($t9) && (LenVec($vec#$1_option_Option'$1_optional_aggregator_Integer'($t9)) <= 1));

    // assume Eq<option::Option<optional_aggregator::Integer>>($t9, option::spec_some<optional_aggregator::Integer>($t8)) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aggregator/optional_aggregator.move:81:26+32
    assume $IsEqual'$1_option_Option'$1_optional_aggregator_Integer''($t9, $1_option_spec_some'$1_optional_aggregator_Integer'($t8));

    // $t9 := opaque end: option::some<optional_aggregator::Integer>($t8) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aggregator/optional_aggregator.move:81:26+32

    // $t2 := pack optional_aggregator::OptionalAggregator($t7, $t9) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aggregator/optional_aggregator.move:79:13+137
    assume {:print "$at(79,2630,2767)"} true;
    $t2 := $1_optional_aggregator_OptionalAggregator($t7, $t9);

    // label L2 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aggregator/optional_aggregator.move:73:9+383
    assume {:print "$at(79,2394,2777)"} true;
L2:

    // trace_return[0]($t2) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aggregator/optional_aggregator.move:73:9+383
    assume {:print "$at(79,2394,2777)"} true;
    assume {:print "$track_return(22,8,0):", $t2} $t2 == $t2;

    // label L3 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aggregator/optional_aggregator.move:84:5+1
    assume {:print "$at(79,2782,2783)"} true;
L3:

    // return $t2 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aggregator/optional_aggregator.move:84:5+1
    assume {:print "$at(79,2782,2783)"} true;
    $ret0 := $t2;
    return;

    // label L4 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aggregator/optional_aggregator.move:84:5+1
L4:

    // abort($t4) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aggregator/optional_aggregator.move:84:5+1
    assume {:print "$at(79,2782,2783)"} true;
    $abort_code := $t4;
    $abort_flag := true;
    return;

}

// fun optional_aggregator::new_integer [baseline] at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aggregator/optional_aggregator.move:26:5+114
procedure {:inline 1} $1_optional_aggregator_new_integer(_$t0: int) returns ($ret0: $1_optional_aggregator_Integer)
{
    // declare local variables
    var $t1: int;
    var $t2: $1_optional_aggregator_Integer;
    var $t0: int;
    var $temp_0'$1_optional_aggregator_Integer': $1_optional_aggregator_Integer;
    var $temp_0'u128': int;
    $t0 := _$t0;

    // bytecode translation starts here
    // trace_local[limit]($t0) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aggregator/optional_aggregator.move:26:5+1
    assume {:print "$at(79,922,923)"} true;
    assume {:print "$track_local(22,9,0):", $t0} $t0 == $t0;

    // $t1 := 0 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aggregator/optional_aggregator.move:28:20+1
    assume {:print "$at(79,999,1000)"} true;
    $t1 := 0;
    assume $IsValid'u128'($t1);

    // $t2 := pack optional_aggregator::Integer($t1, $t0) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aggregator/optional_aggregator.move:27:9+60
    assume {:print "$at(79,970,1030)"} true;
    $t2 := $1_optional_aggregator_Integer($t1, $t0);

    // trace_return[0]($t2) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aggregator/optional_aggregator.move:27:9+60
    assume {:print "$track_return(22,9,0):", $t2} $t2 == $t2;

    // label L1 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aggregator/optional_aggregator.move:31:5+1
    assume {:print "$at(79,1035,1036)"} true;
L1:

    // return $t2 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aggregator/optional_aggregator.move:31:5+1
    assume {:print "$at(79,1035,1036)"} true;
    $ret0 := $t2;
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

// struct coin::FreezeCapability<aptos_coin::AptosCoin> at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.move:136:5+60
type {:datatype} $1_coin_FreezeCapability'$1_aptos_coin_AptosCoin';
function {:constructor} $1_coin_FreezeCapability'$1_aptos_coin_AptosCoin'($dummy_field: bool): $1_coin_FreezeCapability'$1_aptos_coin_AptosCoin';
function {:inline} $Update'$1_coin_FreezeCapability'$1_aptos_coin_AptosCoin''_dummy_field(s: $1_coin_FreezeCapability'$1_aptos_coin_AptosCoin', x: bool): $1_coin_FreezeCapability'$1_aptos_coin_AptosCoin' {
    $1_coin_FreezeCapability'$1_aptos_coin_AptosCoin'(x)
}
function $IsValid'$1_coin_FreezeCapability'$1_aptos_coin_AptosCoin''(s: $1_coin_FreezeCapability'$1_aptos_coin_AptosCoin'): bool {
    $IsValid'bool'($dummy_field#$1_coin_FreezeCapability'$1_aptos_coin_AptosCoin'(s))
}
function {:inline} $IsEqual'$1_coin_FreezeCapability'$1_aptos_coin_AptosCoin''(s1: $1_coin_FreezeCapability'$1_aptos_coin_AptosCoin', s2: $1_coin_FreezeCapability'$1_aptos_coin_AptosCoin'): bool {
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

// fun coin::destroy_freeze_cap<aptos_coin::AptosCoin> [baseline] at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.move:606:5+143
procedure {:inline 1} $1_coin_destroy_freeze_cap'$1_aptos_coin_AptosCoin'(_$t0: $1_coin_FreezeCapability'$1_aptos_coin_AptosCoin') returns ()
{
    // declare local variables
    var $t1: $1_option_Option'$1_optional_aggregator_OptionalAggregator';
    var $t2: bool;
    var $t0: $1_coin_FreezeCapability'$1_aptos_coin_AptosCoin';
    var $temp_0'$1_coin_FreezeCapability'$1_aptos_coin_AptosCoin'': $1_coin_FreezeCapability'$1_aptos_coin_AptosCoin';
    $t0 := _$t0;

    // bytecode translation starts here
    // assume Identical($t1, select coin::CoinInfo.supply(global<coin::CoinInfo<#0>>(select type_info::TypeInfo.account_address(type_info::$type_of<#0>())))) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.spec.move:32:9+99
    assume {:print "$at(94,1664,1763)"} true;
    assume ($t1 == $supply#$1_coin_CoinInfo'$1_aptos_coin_AptosCoin'($ResourceValue($1_coin_CoinInfo'$1_aptos_coin_AptosCoin'_$memory, $account_address#$1_type_info_TypeInfo($1_type_info_TypeInfo(1, Vec(DefaultVecMap()[0 := 97][1 := 112][2 := 116][3 := 111][4 := 115][5 := 95][6 := 99][7 := 111][8 := 105][9 := 110], 10), Vec(DefaultVecMap()[0 := 65][1 := 112][2 := 116][3 := 111][4 := 115][5 := 67][6 := 111][7 := 105][8 := 110], 9))))));

    // trace_local[freeze_cap]($t0) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.move:606:5+1
    assume {:print "$at(93,22830,22831)"} true;
    assume {:print "$track_local(23,9,0):", $t0} $t0 == $t0;

    // $t2 := unpack coin::FreezeCapability<#0>($t0) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.move:607:13+29
    assume {:print "$at(93,22924,22953)"} true;
    $t2 := $dummy_field#$1_coin_FreezeCapability'$1_aptos_coin_AptosCoin'($t0);

    // destroy($t2) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.move:607:13+29

    // label L1 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.move:608:5+1
    assume {:print "$at(93,22972,22973)"} true;
L1:

    // return () at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.move:608:5+1
    assume {:print "$at(93,22972,22973)"} true;
    return;

}

// fun coin::destroy_mint_cap<aptos_coin::AptosCoin> [baseline] at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.move:611:5+133
procedure {:inline 1} $1_coin_destroy_mint_cap'$1_aptos_coin_AptosCoin'(_$t0: $1_coin_MintCapability'$1_aptos_coin_AptosCoin') returns ()
{
    // declare local variables
    var $t1: $1_option_Option'$1_optional_aggregator_OptionalAggregator';
    var $t2: bool;
    var $t0: $1_coin_MintCapability'$1_aptos_coin_AptosCoin';
    var $temp_0'$1_coin_MintCapability'$1_aptos_coin_AptosCoin'': $1_coin_MintCapability'$1_aptos_coin_AptosCoin';
    $t0 := _$t0;

    // bytecode translation starts here
    // assume Identical($t1, select coin::CoinInfo.supply(global<coin::CoinInfo<#0>>(select type_info::TypeInfo.account_address(type_info::$type_of<#0>())))) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.spec.move:32:9+99
    assume {:print "$at(94,1664,1763)"} true;
    assume ($t1 == $supply#$1_coin_CoinInfo'$1_aptos_coin_AptosCoin'($ResourceValue($1_coin_CoinInfo'$1_aptos_coin_AptosCoin'_$memory, $account_address#$1_type_info_TypeInfo($1_type_info_TypeInfo(1, Vec(DefaultVecMap()[0 := 97][1 := 112][2 := 116][3 := 111][4 := 115][5 := 95][6 := 99][7 := 111][8 := 105][9 := 110], 10), Vec(DefaultVecMap()[0 := 65][1 := 112][2 := 116][3 := 111][4 := 115][5 := 67][6 := 111][7 := 105][8 := 110], 9))))));

    // trace_local[mint_cap]($t0) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.move:611:5+1
    assume {:print "$at(93,23014,23015)"} true;
    assume {:print "$track_local(23,10,0):", $t0} $t0 == $t0;

    // $t2 := unpack coin::MintCapability<#0>($t0) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.move:612:13+27
    assume {:print "$at(93,23102,23129)"} true;
    $t2 := $dummy_field#$1_coin_MintCapability'$1_aptos_coin_AptosCoin'($t0);

    // destroy($t2) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.move:612:13+27

    // label L1 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.move:613:5+1
    assume {:print "$at(93,23146,23147)"} true;
L1:

    // return () at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.move:613:5+1
    assume {:print "$at(93,23146,23147)"} true;
    return;

}

// fun coin::initialize_internal<aptos_coin::AptosCoin> [baseline] at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.move:464:5+1268
procedure {:inline 1} $1_coin_initialize_internal'$1_aptos_coin_AptosCoin'(_$t0: $signer, _$t1: $1_string_String, _$t2: $1_string_String, _$t3: int, _$t4: bool, _$t5: bool) returns ($ret0: $1_coin_BurnCapability'$1_aptos_coin_AptosCoin', $ret1: $1_coin_FreezeCapability'$1_aptos_coin_AptosCoin', $ret2: $1_coin_MintCapability'$1_aptos_coin_AptosCoin')
{
    // declare local variables
    var $t6: $1_option_Option'$1_optional_aggregator_OptionalAggregator';
    var $t7: int;
    var $t8: $1_string_String;
    var $t9: $1_string_String;
    var $t10: int;
    var $t11: $1_coin_CoinInfo'$1_aptos_coin_AptosCoin';
    var $t12: int;
    var $t13: int;
    var $t14: int;
    var $t15: int;
    var $t16: int;
    var $t17: $1_option_Option'$1_optional_aggregator_OptionalAggregator';
    var $t18: int;
    var $t19: $1_option_Option'$1_optional_aggregator_OptionalAggregator';
    var $t20: bool;
    var $t21: int;
    var $t22: int;
    var $t23: bool;
    var $t24: bool;
    var $t25: int;
    var $t26: int;
    var $t27: int;
    var $t28: int;
    var $t29: bool;
    var $t30: int;
    var $t31: int;
    var $t32: int;
    var $t33: int;
    var $t34: bool;
    var $t35: int;
    var $t36: int;
    var $t37: int;
    var $t38: $1_optional_aggregator_OptionalAggregator;
    var $t39: $1_coin_CoinInfo'$1_aptos_coin_AptosCoin';
    var $t40: bool;
    var $t41: $1_coin_BurnCapability'$1_aptos_coin_AptosCoin';
    var $t42: bool;
    var $t43: $1_coin_FreezeCapability'$1_aptos_coin_AptosCoin';
    var $t44: bool;
    var $t45: $1_coin_MintCapability'$1_aptos_coin_AptosCoin';
    var $t0: $signer;
    var $t1: $1_string_String;
    var $t2: $1_string_String;
    var $t3: int;
    var $t4: bool;
    var $t5: bool;
    var $1_coin_CoinInfo'$1_aptos_coin_AptosCoin'_$modifies: [int]bool;
    var $temp_0'$1_coin_BurnCapability'$1_aptos_coin_AptosCoin'': $1_coin_BurnCapability'$1_aptos_coin_AptosCoin';
    var $temp_0'$1_coin_CoinInfo'$1_aptos_coin_AptosCoin'': $1_coin_CoinInfo'$1_aptos_coin_AptosCoin';
    var $temp_0'$1_coin_FreezeCapability'$1_aptos_coin_AptosCoin'': $1_coin_FreezeCapability'$1_aptos_coin_AptosCoin';
    var $temp_0'$1_coin_MintCapability'$1_aptos_coin_AptosCoin'': $1_coin_MintCapability'$1_aptos_coin_AptosCoin';
    var $temp_0'$1_string_String': $1_string_String;
    var $temp_0'address': int;
    var $temp_0'bool': bool;
    var $temp_0'signer': $signer;
    var $temp_0'u8': int;
    $t0 := _$t0;
    $t1 := _$t1;
    $t2 := _$t2;
    $t3 := _$t3;
    $t4 := _$t4;
    $t5 := _$t5;

    // bytecode translation starts here
    // assume Identical($t12, signer::$address_of($t0)) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.spec.move:312:9+47
    assume {:print "$at(94,13056,13103)"} true;
    assume ($t12 == $1_signer_$address_of($t0));

    // assume Identical($t13, signer::$address_of($t0)) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.spec.move:292:9+47
    assume {:print "$at(94,12276,12323)"} true;
    assume ($t13 == $1_signer_$address_of($t0));

    // assume Identical($t14, select type_info::TypeInfo.account_address(type_info::$type_of<#0>())) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.spec.move:293:9+66
    assume {:print "$at(94,12332,12398)"} true;
    assume ($t14 == $account_address#$1_type_info_TypeInfo($1_type_info_TypeInfo(1, Vec(DefaultVecMap()[0 := 97][1 := 112][2 := 116][3 := 111][4 := 115][5 := 95][6 := 99][7 := 111][8 := 105][9 := 110], 10), Vec(DefaultVecMap()[0 := 65][1 := 112][2 := 116][3 := 111][4 := 115][5 := 67][6 := 111][7 := 105][8 := 110], 9))));

    // trace_local[account]($t0) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.move:464:5+1
    assume {:print "$at(93,17835,17836)"} true;
    assume {:print "$track_local(23,18,0):", $t0} $t0 == $t0;

    // trace_local[name]($t1) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.move:464:5+1
    assume {:print "$track_local(23,18,1):", $t1} $t1 == $t1;

    // trace_local[symbol]($t2) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.move:464:5+1
    assume {:print "$track_local(23,18,2):", $t2} $t2 == $t2;

    // trace_local[decimals]($t3) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.move:464:5+1
    assume {:print "$track_local(23,18,3):", $t3} $t3 == $t3;

    // trace_local[monitor_supply]($t4) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.move:464:5+1
    assume {:print "$track_local(23,18,4):", $t4} $t4 == $t4;

    // trace_local[parallelizable]($t5) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.move:464:5+1
    assume {:print "$track_local(23,18,5):", $t5} $t5 == $t5;

    // $t15 := signer::address_of($t0) on_abort goto L16 with $t16 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.move:472:28+27
    assume {:print "$at(93,18157,18184)"} true;
    call $t15 := $1_signer_address_of($t0);
    if ($abort_flag) {
        assume {:print "$at(93,18157,18184)"} true;
        $t16 := $abort_code;
        assume {:print "$track_abort(23,18):", $t16} $t16 == $t16;
        goto L16;
    }

    // trace_local[account_addr]($t15) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.move:472:13+12
    assume {:print "$track_local(23,18,10):", $t15} $t15 == $t15;

    // assume Identical($t17, select coin::CoinInfo.supply(global<coin::CoinInfo<#0>>(select type_info::TypeInfo.account_address(type_info::$type_of<#0>())))) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.spec.move:32:9+99
    assume {:print "$at(94,1664,1763)"} true;
    assume ($t17 == $supply#$1_coin_CoinInfo'$1_aptos_coin_AptosCoin'($ResourceValue($1_coin_CoinInfo'$1_aptos_coin_AptosCoin'_$memory, $account_address#$1_type_info_TypeInfo($1_type_info_TypeInfo(1, Vec(DefaultVecMap()[0 := 97][1 := 112][2 := 116][3 := 111][4 := 115][5 := 95][6 := 99][7 := 111][8 := 105][9 := 110], 10), Vec(DefaultVecMap()[0 := 65][1 := 112][2 := 116][3 := 111][4 := 115][5 := 67][6 := 111][7 := 105][8 := 110], 9))))));

    // $t18 := opaque begin: coin::coin_address<#0>() at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.move:475:13+24
    assume {:print "$at(93,18216,18240)"} true;

    // assume WellFormed($t18) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.move:475:13+24
    assume $IsValid'address'($t18);

    // assume Identical($t19, select coin::CoinInfo.supply(global<coin::CoinInfo<#0>>(select type_info::TypeInfo.account_address(type_info::$type_of<#0>())))) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.spec.move:33:9+100
    assume {:print "$at(94,1772,1872)"} true;
    assume ($t19 == $supply#$1_coin_CoinInfo'$1_aptos_coin_AptosCoin'($ResourceValue($1_coin_CoinInfo'$1_aptos_coin_AptosCoin'_$memory, $account_address#$1_type_info_TypeInfo($1_type_info_TypeInfo(1, Vec(DefaultVecMap()[0 := 97][1 := 112][2 := 116][3 := 111][4 := 115][5 := 95][6 := 99][7 := 111][8 := 105][9 := 110], 10), Vec(DefaultVecMap()[0 := 65][1 := 112][2 := 116][3 := 111][4 := 115][5 := 67][6 := 111][7 := 105][8 := 110], 9))))));

    // assume Eq<address>($t18, select type_info::TypeInfo.account_address(type_info::$type_of<#0>())) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.spec.move:33:9+100
    assume $IsEqual'address'($t18, $account_address#$1_type_info_TypeInfo($1_type_info_TypeInfo(1, Vec(DefaultVecMap()[0 := 97][1 := 112][2 := 116][3 := 111][4 := 115][5 := 95][6 := 99][7 := 111][8 := 105][9 := 110], 10), Vec(DefaultVecMap()[0 := 65][1 := 112][2 := 116][3 := 111][4 := 115][5 := 67][6 := 111][7 := 105][8 := 110], 9))));

    // $t18 := opaque end: coin::coin_address<#0>() at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.spec.move:33:9+100

    // $t20 := ==($t18, $t15) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.move:475:38+2
    assume {:print "$at(93,18241,18243)"} true;
    $t20 := $IsEqual'address'($t18, $t15);

    // if ($t20) goto L1 else goto L0 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.move:474:9+138
    assume {:print "$at(93,18195,18333)"} true;
    if ($t20) { goto L1; } else { goto L0; }

    // label L1 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.move:474:9+138
L1:

    // goto L2 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.move:474:9+138
    assume {:print "$at(93,18195,18333)"} true;
    goto L2;

    // label L0 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.move:474:9+138
L0:

    // $t21 := 1 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.move:476:37+27
    assume {:print "$at(93,18294,18321)"} true;
    $t21 := 1;
    assume $IsValid'u64'($t21);

    // $t22 := error::invalid_argument($t21) on_abort goto L16 with $t16 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.move:476:13+52
    call $t22 := $1_error_invalid_argument($t21);
    if ($abort_flag) {
        assume {:print "$at(93,18270,18322)"} true;
        $t16 := $abort_code;
        assume {:print "$track_abort(23,18):", $t16} $t16 == $t16;
        goto L16;
    }

    // trace_abort($t22) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.move:474:9+138
    assume {:print "$at(93,18195,18333)"} true;
    assume {:print "$track_abort(23,18):", $t22} $t22 == $t22;

    // $t16 := move($t22) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.move:474:9+138
    $t16 := $t22;

    // goto L16 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.move:474:9+138
    goto L16;

    // label L2 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.move:480:41+12
    assume {:print "$at(93,18393,18405)"} true;
L2:

    // $t23 := exists<coin::CoinInfo<#0>>($t15) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.move:480:14+6
    assume {:print "$at(93,18366,18372)"} true;
    $t23 := $ResourceExists($1_coin_CoinInfo'$1_aptos_coin_AptosCoin'_$memory, $t15);

    // $t24 := !($t23) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.move:480:13+1
    call $t24 := $Not($t23);

    // if ($t24) goto L4 else goto L3 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.move:479:9+138
    assume {:print "$at(93,18344,18482)"} true;
    if ($t24) { goto L4; } else { goto L3; }

    // label L4 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.move:479:9+138
L4:

    // goto L5 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.move:479:9+138
    assume {:print "$at(93,18344,18482)"} true;
    goto L5;

    // label L3 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.move:479:9+138
L3:

    // $t25 := 2 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.move:481:35+28
    assume {:print "$at(93,18442,18470)"} true;
    $t25 := 2;
    assume $IsValid'u64'($t25);

    // $t26 := error::already_exists($t25) on_abort goto L16 with $t16 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.move:481:13+51
    call $t26 := $1_error_already_exists($t25);
    if ($abort_flag) {
        assume {:print "$at(93,18420,18471)"} true;
        $t16 := $abort_code;
        assume {:print "$track_abort(23,18):", $t16} $t16 == $t16;
        goto L16;
    }

    // trace_abort($t26) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.move:479:9+138
    assume {:print "$at(93,18344,18482)"} true;
    assume {:print "$track_abort(23,18):", $t26} $t26 == $t26;

    // $t16 := move($t26) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.move:479:9+138
    $t16 := $t26;

    // goto L16 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.move:479:9+138
    goto L16;

    // label L5 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.move:484:32+5
    assume {:print "$at(93,18516,18521)"} true;
L5:

    // $t27 := string::length($t1) on_abort goto L16 with $t16 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.move:484:17+21
    assume {:print "$at(93,18501,18522)"} true;
    call $t27 := $1_string_length($t1);
    if ($abort_flag) {
        assume {:print "$at(93,18501,18522)"} true;
        $t16 := $abort_code;
        assume {:print "$track_abort(23,18):", $t16} $t16 == $t16;
        goto L16;
    }

    // $t28 := 32 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.move:484:42+20
    $t28 := 32;
    assume $IsValid'u64'($t28);

    // $t29 := <=($t27, $t28) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.move:484:39+2
    call $t29 := $Le($t27, $t28);

    // if ($t29) goto L7 else goto L6 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.move:484:9+100
    if ($t29) { goto L7; } else { goto L6; }

    // label L7 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.move:484:9+100
L7:

    // goto L8 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.move:484:9+100
    assume {:print "$at(93,18493,18593)"} true;
    goto L8;

    // label L6 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.move:484:9+100
L6:

    // $t30 := 12 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.move:484:88+19
    assume {:print "$at(93,18572,18591)"} true;
    $t30 := 12;
    assume $IsValid'u64'($t30);

    // $t31 := error::invalid_argument($t30) on_abort goto L16 with $t16 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.move:484:64+44
    call $t31 := $1_error_invalid_argument($t30);
    if ($abort_flag) {
        assume {:print "$at(93,18548,18592)"} true;
        $t16 := $abort_code;
        assume {:print "$track_abort(23,18):", $t16} $t16 == $t16;
        goto L16;
    }

    // trace_abort($t31) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.move:484:9+100
    assume {:print "$at(93,18493,18593)"} true;
    assume {:print "$track_abort(23,18):", $t31} $t31 == $t31;

    // $t16 := move($t31) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.move:484:9+100
    $t16 := $t31;

    // goto L16 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.move:484:9+100
    goto L16;

    // label L8 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.move:485:32+7
    assume {:print "$at(93,18626,18633)"} true;
L8:

    // $t32 := string::length($t2) on_abort goto L16 with $t16 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.move:485:17+23
    assume {:print "$at(93,18611,18634)"} true;
    call $t32 := $1_string_length($t2);
    if ($abort_flag) {
        assume {:print "$at(93,18611,18634)"} true;
        $t16 := $abort_code;
        assume {:print "$track_abort(23,18):", $t16} $t16 == $t16;
        goto L16;
    }

    // $t33 := 10 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.move:485:44+22
    $t33 := 10;
    assume $IsValid'u64'($t33);

    // $t34 := <=($t32, $t33) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.move:485:41+2
    call $t34 := $Le($t32, $t33);

    // if ($t34) goto L10 else goto L9 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.move:485:9+106
    if ($t34) { goto L10; } else { goto L9; }

    // label L10 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.move:485:9+106
L10:

    // goto L11 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.move:485:9+106
    assume {:print "$at(93,18603,18709)"} true;
    goto L11;

    // label L9 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.move:485:9+106
L9:

    // $t35 := 13 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.move:485:92+21
    assume {:print "$at(93,18686,18707)"} true;
    $t35 := 13;
    assume $IsValid'u64'($t35);

    // $t36 := error::invalid_argument($t35) on_abort goto L16 with $t16 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.move:485:68+46
    call $t36 := $1_error_invalid_argument($t35);
    if ($abort_flag) {
        assume {:print "$at(93,18662,18708)"} true;
        $t16 := $abort_code;
        assume {:print "$track_abort(23,18):", $t16} $t16 == $t16;
        goto L16;
    }

    // trace_abort($t36) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.move:485:9+106
    assume {:print "$at(93,18603,18709)"} true;
    assume {:print "$track_abort(23,18):", $t36} $t36 == $t36;

    // $t16 := move($t36) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.move:485:9+106
    $t16 := $t36;

    // goto L16 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.move:485:9+106
    goto L16;

    // label L11 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.move:488:13+4
    assume {:print "$at(93,18769,18773)"} true;
L11:

    // if ($t4) goto L13 else goto L12 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.move:491:21+112
    assume {:print "$at(93,18837,18949)"} true;
    if ($t4) { goto L13; } else { goto L12; }

    // label L13 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.move:491:81+8
L13:

    // $t37 := 340282366920938463463374607431768211455 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.move:491:81+8
    assume {:print "$at(93,18897,18905)"} true;
    $t37 := 340282366920938463463374607431768211455;
    assume $IsValid'u128'($t37);

    // $t38 := optional_aggregator::new($t37, $t5) on_abort goto L16 with $t16 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.move:491:56+50
    call $t38 := $1_optional_aggregator_new($t37, $t5);
    if ($abort_flag) {
        assume {:print "$at(93,18872,18922)"} true;
        $t16 := $abort_code;
        assume {:print "$track_abort(23,18):", $t16} $t16 == $t16;
        goto L16;
    }

    // $t6 := opaque begin: option::some<optional_aggregator::OptionalAggregator>($t38) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.move:491:43+64

    // assume And(WellFormed($t6), And(Le(Len<optional_aggregator::OptionalAggregator>(select option::Option.vec($t6)), 1), forall $elem: select option::Option.vec($t6): And(And(And(And(And(Iff(option::$is_some<aggregator::Aggregator>(select optional_aggregator::OptionalAggregator.aggregator($elem)), option::$is_none<optional_aggregator::Integer>(select optional_aggregator::OptionalAggregator.integer($elem))), Iff(option::$is_some<optional_aggregator::Integer>(select optional_aggregator::OptionalAggregator.integer($elem)), option::$is_none<aggregator::Aggregator>(select optional_aggregator::OptionalAggregator.aggregator($elem)))), Implies(option::$is_some<optional_aggregator::Integer>(select optional_aggregator::OptionalAggregator.integer($elem)), Le(select optional_aggregator::Integer.value(option::$borrow<optional_aggregator::Integer>(select optional_aggregator::OptionalAggregator.integer($elem))), select optional_aggregator::Integer.limit(option::$borrow<optional_aggregator::Integer>(select optional_aggregator::OptionalAggregator.integer($elem)))))), Implies(option::$is_some<aggregator::Aggregator>(select optional_aggregator::OptionalAggregator.aggregator($elem)), Le(aggregator::spec_aggregator_get_val(option::$borrow<aggregator::Aggregator>(select optional_aggregator::OptionalAggregator.aggregator($elem))), aggregator::spec_get_limit(option::$borrow<aggregator::Aggregator>(select optional_aggregator::OptionalAggregator.aggregator($elem)))))), Le(Len<aggregator::Aggregator>(select option::Option.vec(select optional_aggregator::OptionalAggregator.aggregator($elem))), 1)), Le(Len<optional_aggregator::Integer>(select option::Option.vec(select optional_aggregator::OptionalAggregator.integer($elem))), 1)))) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.move:491:43+64
    assume ($IsValid'$1_option_Option'$1_optional_aggregator_OptionalAggregator''($t6) && ((LenVec($vec#$1_option_Option'$1_optional_aggregator_OptionalAggregator'($t6)) <= 1) && (var $range_0 := $vec#$1_option_Option'$1_optional_aggregator_OptionalAggregator'($t6); (forall $i_1: int :: InRangeVec($range_0, $i_1) ==> (var $elem := ReadVec($range_0, $i_1);
    ((((((($1_option_$is_some'$1_aggregator_Aggregator'($aggregator#$1_optional_aggregator_OptionalAggregator($elem)) <==> $1_option_$is_none'$1_optional_aggregator_Integer'($integer#$1_optional_aggregator_OptionalAggregator($elem))) && ($1_option_$is_some'$1_optional_aggregator_Integer'($integer#$1_optional_aggregator_OptionalAggregator($elem)) <==> $1_option_$is_none'$1_aggregator_Aggregator'($aggregator#$1_optional_aggregator_OptionalAggregator($elem)))) && ($1_option_$is_some'$1_optional_aggregator_Integer'($integer#$1_optional_aggregator_OptionalAggregator($elem)) ==> ($value#$1_optional_aggregator_Integer($1_option_$borrow'$1_optional_aggregator_Integer'($integer#$1_optional_aggregator_OptionalAggregator($elem))) <= $limit#$1_optional_aggregator_Integer($1_option_$borrow'$1_optional_aggregator_Integer'($integer#$1_optional_aggregator_OptionalAggregator($elem)))))) && ($1_option_$is_some'$1_aggregator_Aggregator'($aggregator#$1_optional_aggregator_OptionalAggregator($elem)) ==> ($1_aggregator_spec_aggregator_get_val($1_option_$borrow'$1_aggregator_Aggregator'($aggregator#$1_optional_aggregator_OptionalAggregator($elem))) <= $1_aggregator_spec_get_limit($1_option_$borrow'$1_aggregator_Aggregator'($aggregator#$1_optional_aggregator_OptionalAggregator($elem)))))) && (LenVec($vec#$1_option_Option'$1_aggregator_Aggregator'($aggregator#$1_optional_aggregator_OptionalAggregator($elem))) <= 1)) && (LenVec($vec#$1_option_Option'$1_optional_aggregator_Integer'($integer#$1_optional_aggregator_OptionalAggregator($elem))) <= 1))))))));

    // assume Eq<option::Option<optional_aggregator::OptionalAggregator>>($t6, option::spec_some<optional_aggregator::OptionalAggregator>($t38)) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.move:491:43+64
    assume $IsEqual'$1_option_Option'$1_optional_aggregator_OptionalAggregator''($t6, $1_option_spec_some'$1_optional_aggregator_OptionalAggregator'($t38));

    // $t6 := opaque end: option::some<optional_aggregator::OptionalAggregator>($t38) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.move:491:43+64

    // goto L14 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.move:491:21+112
    goto L14;

    // label L12 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.move:491:117+14
L12:

    // $t6 := opaque begin: option::none<optional_aggregator::OptionalAggregator>() at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.move:491:117+14
    assume {:print "$at(93,18933,18947)"} true;

    // assume And(WellFormed($t6), And(Le(Len<optional_aggregator::OptionalAggregator>(select option::Option.vec($t6)), 1), forall $elem: select option::Option.vec($t6): And(And(And(And(And(Iff(option::$is_some<aggregator::Aggregator>(select optional_aggregator::OptionalAggregator.aggregator($elem)), option::$is_none<optional_aggregator::Integer>(select optional_aggregator::OptionalAggregator.integer($elem))), Iff(option::$is_some<optional_aggregator::Integer>(select optional_aggregator::OptionalAggregator.integer($elem)), option::$is_none<aggregator::Aggregator>(select optional_aggregator::OptionalAggregator.aggregator($elem)))), Implies(option::$is_some<optional_aggregator::Integer>(select optional_aggregator::OptionalAggregator.integer($elem)), Le(select optional_aggregator::Integer.value(option::$borrow<optional_aggregator::Integer>(select optional_aggregator::OptionalAggregator.integer($elem))), select optional_aggregator::Integer.limit(option::$borrow<optional_aggregator::Integer>(select optional_aggregator::OptionalAggregator.integer($elem)))))), Implies(option::$is_some<aggregator::Aggregator>(select optional_aggregator::OptionalAggregator.aggregator($elem)), Le(aggregator::spec_aggregator_get_val(option::$borrow<aggregator::Aggregator>(select optional_aggregator::OptionalAggregator.aggregator($elem))), aggregator::spec_get_limit(option::$borrow<aggregator::Aggregator>(select optional_aggregator::OptionalAggregator.aggregator($elem)))))), Le(Len<aggregator::Aggregator>(select option::Option.vec(select optional_aggregator::OptionalAggregator.aggregator($elem))), 1)), Le(Len<optional_aggregator::Integer>(select option::Option.vec(select optional_aggregator::OptionalAggregator.integer($elem))), 1)))) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.move:491:117+14
    assume ($IsValid'$1_option_Option'$1_optional_aggregator_OptionalAggregator''($t6) && ((LenVec($vec#$1_option_Option'$1_optional_aggregator_OptionalAggregator'($t6)) <= 1) && (var $range_0 := $vec#$1_option_Option'$1_optional_aggregator_OptionalAggregator'($t6); (forall $i_1: int :: InRangeVec($range_0, $i_1) ==> (var $elem := ReadVec($range_0, $i_1);
    ((((((($1_option_$is_some'$1_aggregator_Aggregator'($aggregator#$1_optional_aggregator_OptionalAggregator($elem)) <==> $1_option_$is_none'$1_optional_aggregator_Integer'($integer#$1_optional_aggregator_OptionalAggregator($elem))) && ($1_option_$is_some'$1_optional_aggregator_Integer'($integer#$1_optional_aggregator_OptionalAggregator($elem)) <==> $1_option_$is_none'$1_aggregator_Aggregator'($aggregator#$1_optional_aggregator_OptionalAggregator($elem)))) && ($1_option_$is_some'$1_optional_aggregator_Integer'($integer#$1_optional_aggregator_OptionalAggregator($elem)) ==> ($value#$1_optional_aggregator_Integer($1_option_$borrow'$1_optional_aggregator_Integer'($integer#$1_optional_aggregator_OptionalAggregator($elem))) <= $limit#$1_optional_aggregator_Integer($1_option_$borrow'$1_optional_aggregator_Integer'($integer#$1_optional_aggregator_OptionalAggregator($elem)))))) && ($1_option_$is_some'$1_aggregator_Aggregator'($aggregator#$1_optional_aggregator_OptionalAggregator($elem)) ==> ($1_aggregator_spec_aggregator_get_val($1_option_$borrow'$1_aggregator_Aggregator'($aggregator#$1_optional_aggregator_OptionalAggregator($elem))) <= $1_aggregator_spec_get_limit($1_option_$borrow'$1_aggregator_Aggregator'($aggregator#$1_optional_aggregator_OptionalAggregator($elem)))))) && (LenVec($vec#$1_option_Option'$1_aggregator_Aggregator'($aggregator#$1_optional_aggregator_OptionalAggregator($elem))) <= 1)) && (LenVec($vec#$1_option_Option'$1_optional_aggregator_Integer'($integer#$1_optional_aggregator_OptionalAggregator($elem))) <= 1))))))));

    // assume Eq<option::Option<optional_aggregator::OptionalAggregator>>($t6, option::spec_none<optional_aggregator::OptionalAggregator>()) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.move:491:117+14
    assume $IsEqual'$1_option_Option'$1_optional_aggregator_OptionalAggregator''($t6, $1_option_spec_none'$1_optional_aggregator_OptionalAggregator'());

    // $t6 := opaque end: option::none<optional_aggregator::OptionalAggregator>() at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.move:491:117+14

    // label L14 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.move:488:13+4
    assume {:print "$at(93,18769,18773)"} true;
L14:

    // $t39 := pack coin::CoinInfo<#0>($t1, $t2, $t3, $t6) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.move:487:25+224
    assume {:print "$at(93,18736,18960)"} true;
    $t39 := $1_coin_CoinInfo'$1_aptos_coin_AptosCoin'($t1, $t2, $t3, $t6);

    // trace_local[coin_info]($t39) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.move:487:13+9
    assume {:print "$track_local(23,18,11):", $t39} $t39 == $t39;

    // move_to<coin::CoinInfo<#0>>($t39, $t0) on_abort goto L16 with $t16 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.move:493:9+7
    assume {:print "$at(93,18970,18977)"} true;
    if ($ResourceExists($1_coin_CoinInfo'$1_aptos_coin_AptosCoin'_$memory, $addr#$signer($t0))) {
        call $ExecFailureAbort();
    } else {
        $1_coin_CoinInfo'$1_aptos_coin_AptosCoin'_$memory := $ResourceUpdate($1_coin_CoinInfo'$1_aptos_coin_AptosCoin'_$memory, $addr#$signer($t0), $t39);
    }
    if ($abort_flag) {
        assume {:print "$at(93,18970,18977)"} true;
        $t16 := $abort_code;
        assume {:print "$track_abort(23,18):", $t16} $t16 == $t16;
        goto L16;
    }

    // $t40 := false at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.move:495:10+27
    assume {:print "$at(93,19009,19036)"} true;
    $t40 := false;
    assume $IsValid'bool'($t40);

    // $t41 := pack coin::BurnCapability<#0>($t40) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.move:495:10+27
    $t41 := $1_coin_BurnCapability'$1_aptos_coin_AptosCoin'($t40);

    // $t42 := false at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.move:495:39+29
    $t42 := false;
    assume $IsValid'bool'($t42);

    // $t43 := pack coin::FreezeCapability<#0>($t42) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.move:495:39+29
    $t43 := $1_coin_FreezeCapability'$1_aptos_coin_AptosCoin'($t42);

    // $t44 := false at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.move:495:70+27
    $t44 := false;
    assume $IsValid'bool'($t44);

    // $t45 := pack coin::MintCapability<#0>($t44) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.move:495:70+27
    $t45 := $1_coin_MintCapability'$1_aptos_coin_AptosCoin'($t44);

    // trace_return[0]($t41) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.move:495:9+89
    assume {:print "$track_return(23,18,0):", $t41} $t41 == $t41;

    // trace_return[1]($t43) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.move:495:9+89
    assume {:print "$track_return(23,18,1):", $t43} $t43 == $t43;

    // trace_return[2]($t45) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.move:495:9+89
    assume {:print "$track_return(23,18,2):", $t45} $t45 == $t45;

    // label L15 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.move:496:5+1
    assume {:print "$at(93,19102,19103)"} true;
L15:

    // return ($t41, $t43, $t45) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.move:496:5+1
    assume {:print "$at(93,19102,19103)"} true;
    $ret0 := $t41;
    $ret1 := $t43;
    $ret2 := $t45;
    return;

    // label L16 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.move:496:5+1
L16:

    // abort($t16) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.move:496:5+1
    assume {:print "$at(93,19102,19103)"} true;
    $abort_code := $t16;
    $abort_flag := true;
    return;

}

// fun coin::initialize_with_parallelizable_supply<aptos_coin::AptosCoin> [baseline] at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.move:453:5+445
procedure {:inline 1} $1_coin_initialize_with_parallelizable_supply'$1_aptos_coin_AptosCoin'(_$t0: $signer, _$t1: $1_string_String, _$t2: $1_string_String, _$t3: int, _$t4: bool) returns ($ret0: $1_coin_BurnCapability'$1_aptos_coin_AptosCoin', $ret1: $1_coin_FreezeCapability'$1_aptos_coin_AptosCoin', $ret2: $1_coin_MintCapability'$1_aptos_coin_AptosCoin')
{
    // declare local variables
    var $t5: int;
    var $t6: int;
    var $t7: int;
    var $t8: bool;
    var $t9: int;
    var $t10: bool;
    var $t11: int;
    var $t12: int;
    var $t13: int;
    var $t14: $1_coin_BurnCapability'$1_aptos_coin_AptosCoin';
    var $t15: $1_coin_FreezeCapability'$1_aptos_coin_AptosCoin';
    var $t16: $1_coin_MintCapability'$1_aptos_coin_AptosCoin';
    var $t0: $signer;
    var $t1: $1_string_String;
    var $t2: $1_string_String;
    var $t3: int;
    var $t4: bool;
    var $temp_0'$1_coin_BurnCapability'$1_aptos_coin_AptosCoin'': $1_coin_BurnCapability'$1_aptos_coin_AptosCoin';
    var $temp_0'$1_coin_FreezeCapability'$1_aptos_coin_AptosCoin'': $1_coin_FreezeCapability'$1_aptos_coin_AptosCoin';
    var $temp_0'$1_coin_MintCapability'$1_aptos_coin_AptosCoin'': $1_coin_MintCapability'$1_aptos_coin_AptosCoin';
    var $temp_0'$1_string_String': $1_string_String;
    var $temp_0'bool': bool;
    var $temp_0'signer': $signer;
    var $temp_0'u8': int;
    $t0 := _$t0;
    $t1 := _$t1;
    $t2 := _$t2;
    $t3 := _$t3;
    $t4 := _$t4;

    // bytecode translation starts here
    // assume Identical($t5, signer::$address_of($t0)) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.spec.move:278:9+39
    assume {:print "$at(94,11808,11847)"} true;
    assume ($t5 == $1_signer_$address_of($t0));

    // assume Identical($t6, signer::$address_of($t0)) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.spec.move:292:9+47
    assume {:print "$at(94,12276,12323)"} true;
    assume ($t6 == $1_signer_$address_of($t0));

    // assume Identical($t7, select type_info::TypeInfo.account_address(type_info::$type_of<#0>())) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.spec.move:293:9+66
    assume {:print "$at(94,12332,12398)"} true;
    assume ($t7 == $account_address#$1_type_info_TypeInfo($1_type_info_TypeInfo(1, Vec(DefaultVecMap()[0 := 97][1 := 112][2 := 116][3 := 111][4 := 115][5 := 95][6 := 99][7 := 111][8 := 105][9 := 110], 10), Vec(DefaultVecMap()[0 := 65][1 := 112][2 := 116][3 := 111][4 := 115][5 := 67][6 := 111][7 := 105][8 := 110], 9))));

    // trace_local[account]($t0) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.move:453:5+1
    assume {:print "$at(93,17384,17385)"} true;
    assume {:print "$track_local(23,20,0):", $t0} $t0 == $t0;

    // trace_local[name]($t1) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.move:453:5+1
    assume {:print "$track_local(23,20,1):", $t1} $t1 == $t1;

    // trace_local[symbol]($t2) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.move:453:5+1
    assume {:print "$track_local(23,20,2):", $t2} $t2 == $t2;

    // trace_local[decimals]($t3) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.move:453:5+1
    assume {:print "$track_local(23,20,3):", $t3} $t3 == $t3;

    // trace_local[monitor_supply]($t4) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.move:453:5+1
    assume {:print "$track_local(23,20,4):", $t4} $t4 == $t4;

    // opaque begin: system_addresses::assert_aptos_framework($t0) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.move:460:9+49
    assume {:print "$at(93,17690,17739)"} true;

    // assume Identical($t8, Neq<address>(signer::$address_of($t0), 0x1)) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.move:460:9+49
    assume ($t8 == !$IsEqual'address'($1_signer_$address_of($t0), 1));

    // if ($t8) goto L4 else goto L3 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.move:460:9+49
    if ($t8) { goto L4; } else { goto L3; }

    // label L4 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.move:460:9+49
L4:

    // assume And(Neq<address>(signer::$address_of($t0), 0x1), Eq(5, $t9)) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.move:460:9+49
    assume {:print "$at(93,17690,17739)"} true;
    assume (!$IsEqual'address'($1_signer_$address_of($t0), 1) && $IsEqual'num'(5, $t9));

    // trace_abort($t9) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.move:460:9+49
    assume {:print "$at(93,17690,17739)"} true;
    assume {:print "$track_abort(23,20):", $t9} $t9 == $t9;

    // goto L2 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.move:460:9+49
    goto L2;

    // label L3 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.move:460:9+49
L3:

    // opaque end: system_addresses::assert_aptos_framework($t0) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.move:460:9+49
    assume {:print "$at(93,17690,17739)"} true;

    // $t10 := true at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.move:461:78+4
    assume {:print "$at(93,17818,17822)"} true;
    $t10 := true;
    assume $IsValid'bool'($t10);

    // assume Identical($t11, signer::$address_of($t0)) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.spec.move:312:9+47
    assume {:print "$at(94,13056,13103)"} true;
    assume ($t11 == $1_signer_$address_of($t0));

    // assume Identical($t12, signer::$address_of($t0)) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.spec.move:292:9+47
    assume {:print "$at(94,12276,12323)"} true;
    assume ($t12 == $1_signer_$address_of($t0));

    // assume Identical($t13, select type_info::TypeInfo.account_address(type_info::$type_of<#0>())) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.spec.move:293:9+66
    assume {:print "$at(94,12332,12398)"} true;
    assume ($t13 == $account_address#$1_type_info_TypeInfo($1_type_info_TypeInfo(1, Vec(DefaultVecMap()[0 := 97][1 := 112][2 := 116][3 := 111][4 := 115][5 := 95][6 := 99][7 := 111][8 := 105][9 := 110], 10), Vec(DefaultVecMap()[0 := 65][1 := 112][2 := 116][3 := 111][4 := 115][5 := 67][6 := 111][7 := 105][8 := 110], 9))));

    // ($t14, $t15, $t16) := coin::initialize_internal<#0>($t0, $t1, $t2, $t3, $t4, $t10) on_abort goto L2 with $t9 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.move:461:9+74
    assume {:print "$at(93,17749,17823)"} true;
    call $t14,$t15,$t16 := $1_coin_initialize_internal'$1_aptos_coin_AptosCoin'($t0, $t1, $t2, $t3, $t4, $t10);
    if ($abort_flag) {
        assume {:print "$at(93,17749,17823)"} true;
        $t9 := $abort_code;
        assume {:print "$track_abort(23,20):", $t9} $t9 == $t9;
        goto L2;
    }

    // trace_return[0]($t14) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.move:461:9+74
    assume {:print "$track_return(23,20,0):", $t14} $t14 == $t14;

    // trace_return[1]($t15) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.move:461:9+74
    assume {:print "$track_return(23,20,1):", $t15} $t15 == $t15;

    // trace_return[2]($t16) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.move:461:9+74
    assume {:print "$track_return(23,20,2):", $t16} $t16 == $t16;

    // label L1 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.move:462:5+1
    assume {:print "$at(93,17828,17829)"} true;
L1:

    // return ($t14, $t15, $t16) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.move:462:5+1
    assume {:print "$at(93,17828,17829)"} true;
    $ret0 := $t14;
    $ret1 := $t15;
    $ret2 := $t16;
    return;

    // label L2 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.move:462:5+1
L2:

    // abort($t9) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.move:462:5+1
    assume {:print "$at(93,17828,17829)"} true;
    $abort_code := $t9;
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

// struct aptos_coin::DelegatedMintCapability at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:29:5+68
type {:datatype} $1_aptos_coin_DelegatedMintCapability;
function {:constructor} $1_aptos_coin_DelegatedMintCapability($to: int): $1_aptos_coin_DelegatedMintCapability;
function {:inline} $Update'$1_aptos_coin_DelegatedMintCapability'_to(s: $1_aptos_coin_DelegatedMintCapability, x: int): $1_aptos_coin_DelegatedMintCapability {
    $1_aptos_coin_DelegatedMintCapability(x)
}
function $IsValid'$1_aptos_coin_DelegatedMintCapability'(s: $1_aptos_coin_DelegatedMintCapability): bool {
    $IsValid'address'($to#$1_aptos_coin_DelegatedMintCapability(s))
}
function {:inline} $IsEqual'$1_aptos_coin_DelegatedMintCapability'(s1: $1_aptos_coin_DelegatedMintCapability, s2: $1_aptos_coin_DelegatedMintCapability): bool {
    s1 == s2
}

// struct aptos_coin::Delegations at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:34:5+82
type {:datatype} $1_aptos_coin_Delegations;
function {:constructor} $1_aptos_coin_Delegations($inner: Vec ($1_aptos_coin_DelegatedMintCapability)): $1_aptos_coin_Delegations;
function {:inline} $Update'$1_aptos_coin_Delegations'_inner(s: $1_aptos_coin_Delegations, x: Vec ($1_aptos_coin_DelegatedMintCapability)): $1_aptos_coin_Delegations {
    $1_aptos_coin_Delegations(x)
}
function $IsValid'$1_aptos_coin_Delegations'(s: $1_aptos_coin_Delegations): bool {
    $IsValid'vec'$1_aptos_coin_DelegatedMintCapability''($inner#$1_aptos_coin_Delegations(s))
}
function {:inline} $IsEqual'$1_aptos_coin_Delegations'(s1: $1_aptos_coin_Delegations, s2: $1_aptos_coin_Delegations): bool {
    $IsEqual'vec'$1_aptos_coin_DelegatedMintCapability''($inner#$1_aptos_coin_Delegations(s1), $inner#$1_aptos_coin_Delegations(s2))}
var $1_aptos_coin_Delegations_$memory: $Memory $1_aptos_coin_Delegations;

// struct aptos_coin::MintCapStore at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:24:5+80
type {:datatype} $1_aptos_coin_MintCapStore;
function {:constructor} $1_aptos_coin_MintCapStore($mint_cap: $1_coin_MintCapability'$1_aptos_coin_AptosCoin'): $1_aptos_coin_MintCapStore;
function {:inline} $Update'$1_aptos_coin_MintCapStore'_mint_cap(s: $1_aptos_coin_MintCapStore, x: $1_coin_MintCapability'$1_aptos_coin_AptosCoin'): $1_aptos_coin_MintCapStore {
    $1_aptos_coin_MintCapStore(x)
}
function $IsValid'$1_aptos_coin_MintCapStore'(s: $1_aptos_coin_MintCapStore): bool {
    $IsValid'$1_coin_MintCapability'$1_aptos_coin_AptosCoin''($mint_cap#$1_aptos_coin_MintCapStore(s))
}
function {:inline} $IsEqual'$1_aptos_coin_MintCapStore'(s1: $1_aptos_coin_MintCapStore, s2: $1_aptos_coin_MintCapStore): bool {
    s1 == s2
}
var $1_aptos_coin_MintCapStore_$memory: $Memory $1_aptos_coin_MintCapStore;

// fun aptos_coin::initialize [verification] at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:39:5+760
procedure {:timeLimit 40} $1_aptos_coin_initialize$verify(_$t0: $signer) returns ($ret0: $1_coin_BurnCapability'$1_aptos_coin_AptosCoin', $ret1: $1_coin_MintCapability'$1_aptos_coin_AptosCoin')
{
    // declare local variables
    var $t1: $1_coin_BurnCapability'$1_aptos_coin_AptosCoin';
    var $t2: $1_coin_FreezeCapability'$1_aptos_coin_AptosCoin';
    var $t3: $1_coin_MintCapability'$1_aptos_coin_AptosCoin';
    var $t4: int;
    var $t5: int;
    var $t6: int;
    var $t7: int;
    var $t8: int;
    var $t9: int;
    var $t10: $1_type_info_TypeInfo;
    var $t11: int;
    var $t12: int;
    var $t13: bool;
    var $t14: int;
    var $t15: Vec (int);
    var $t16: $1_string_String;
    var $t17: Vec (int);
    var $t18: $1_string_String;
    var $t19: int;
    var $t20: bool;
    var $t21: int;
    var $t22: int;
    var $t23: int;
    var $t24: $1_coin_BurnCapability'$1_aptos_coin_AptosCoin';
    var $t25: $1_coin_FreezeCapability'$1_aptos_coin_AptosCoin';
    var $t26: $1_coin_MintCapability'$1_aptos_coin_AptosCoin';
    var $t27: $1_aptos_coin_MintCapStore;
    var $t28: $1_option_Option'$1_optional_aggregator_OptionalAggregator';
    var $t29: bool;
    var $t30: bool;
    var $t31: bool;
    var $t32: bool;
    var $t33: bool;
    var $t34: bool;
    var $t35: bool;
    var $t36: bool;
    var $t37: bool;
    var $t38: bool;
    var $t39: bool;
    var $t40: bool;
    var $t41: bool;
    var $t42: bool;
    var $t43: bool;
    var $t44: bool;
    var $t45: bool;
    var $t46: bool;
    var $t47: $1_coin_CoinInfo'$1_aptos_coin_AptosCoin';
    var $t48: $1_optional_aggregator_OptionalAggregator;
    var $t49: int;
    var $t50: bool;
    var $t51: bool;
    var $t52: bool;
    var $t53: bool;
    var $t54: bool;
    var $t55: bool;
    var $t56: bool;
    var $t57: bool;
    var $t58: bool;
    var $t59: bool;
    var $t60: bool;
    var $t61: bool;
    var $t62: bool;
    var $t63: bool;
    var $t64: bool;
    var $t65: bool;
    var $t66: bool;
    var $t0: $signer;
    var $temp_0'$1_coin_BurnCapability'$1_aptos_coin_AptosCoin'': $1_coin_BurnCapability'$1_aptos_coin_AptosCoin';
    var $temp_0'$1_coin_CoinInfo'$1_aptos_coin_AptosCoin'': $1_coin_CoinInfo'$1_aptos_coin_AptosCoin';
    var $temp_0'$1_coin_FreezeCapability'$1_aptos_coin_AptosCoin'': $1_coin_FreezeCapability'$1_aptos_coin_AptosCoin';
    var $temp_0'$1_coin_MintCapability'$1_aptos_coin_AptosCoin'': $1_coin_MintCapability'$1_aptos_coin_AptosCoin';
    var $temp_0'$1_optional_aggregator_OptionalAggregator': $1_optional_aggregator_OptionalAggregator;
    var $temp_0'$1_type_info_TypeInfo': $1_type_info_TypeInfo;
    var $temp_0'address': int;
    var $temp_0'bool': bool;
    var $temp_0'signer': $signer;
    var $temp_0'u128': int;
    var $1_coin_CoinInfo'$1_aptos_coin_AptosCoin'_$memory#27: $Memory $1_coin_CoinInfo'$1_aptos_coin_AptosCoin';
    var $1_aggregator_factory_AggregatorFactory_$memory#28: $Memory $1_aggregator_factory_AggregatorFactory;
    var $1_aptos_coin_MintCapStore_$memory#29: $Memory $1_aptos_coin_MintCapStore;
    $t0 := _$t0;

    // verification entrypoint assumptions
    call $InitVerification();

    // bytecode translation starts here
    // assume WellFormed($t0) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:39:5+1
    assume {:print "$at(2,1298,1299)"} true;
    assume $IsValid'signer'($t0) && $1_signer_is_txn_signer($t0) && $1_signer_is_txn_signer_addr($addr#$signer($t0));

    // assume forall $rsc: ResourceDomain<aggregator_factory::AggregatorFactory>(): WellFormed($rsc) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:39:5+1
    assume (forall $a_0: int :: {$ResourceValue($1_aggregator_factory_AggregatorFactory_$memory, $a_0)}(var $rsc := $ResourceValue($1_aggregator_factory_AggregatorFactory_$memory, $a_0);
    ($IsValid'$1_aggregator_factory_AggregatorFactory'($rsc))));

    // assume forall $rsc: ResourceDomain<coin::CoinInfo<aptos_coin::AptosCoin>>(): And(WellFormed($rsc), And(Le(Len<optional_aggregator::OptionalAggregator>(select option::Option.vec(select coin::CoinInfo.supply($rsc))), 1), forall $elem: select option::Option.vec(select coin::CoinInfo.supply($rsc)): And(And(And(And(And(Iff(option::$is_some<aggregator::Aggregator>(select optional_aggregator::OptionalAggregator.aggregator($elem)), option::$is_none<optional_aggregator::Integer>(select optional_aggregator::OptionalAggregator.integer($elem))), Iff(option::$is_some<optional_aggregator::Integer>(select optional_aggregator::OptionalAggregator.integer($elem)), option::$is_none<aggregator::Aggregator>(select optional_aggregator::OptionalAggregator.aggregator($elem)))), Implies(option::$is_some<optional_aggregator::Integer>(select optional_aggregator::OptionalAggregator.integer($elem)), Le(select optional_aggregator::Integer.value(option::$borrow<optional_aggregator::Integer>(select optional_aggregator::OptionalAggregator.integer($elem))), select optional_aggregator::Integer.limit(option::$borrow<optional_aggregator::Integer>(select optional_aggregator::OptionalAggregator.integer($elem)))))), Implies(option::$is_some<aggregator::Aggregator>(select optional_aggregator::OptionalAggregator.aggregator($elem)), Le(aggregator::spec_aggregator_get_val(option::$borrow<aggregator::Aggregator>(select optional_aggregator::OptionalAggregator.aggregator($elem))), aggregator::spec_get_limit(option::$borrow<aggregator::Aggregator>(select optional_aggregator::OptionalAggregator.aggregator($elem)))))), Le(Len<aggregator::Aggregator>(select option::Option.vec(select optional_aggregator::OptionalAggregator.aggregator($elem))), 1)), Le(Len<optional_aggregator::Integer>(select option::Option.vec(select optional_aggregator::OptionalAggregator.integer($elem))), 1)))) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:39:5+1
    assume (forall $a_0: int :: {$ResourceValue($1_coin_CoinInfo'$1_aptos_coin_AptosCoin'_$memory, $a_0)}(var $rsc := $ResourceValue($1_coin_CoinInfo'$1_aptos_coin_AptosCoin'_$memory, $a_0);
    (($IsValid'$1_coin_CoinInfo'$1_aptos_coin_AptosCoin''($rsc) && ((LenVec($vec#$1_option_Option'$1_optional_aggregator_OptionalAggregator'($supply#$1_coin_CoinInfo'$1_aptos_coin_AptosCoin'($rsc))) <= 1) && (var $range_1 := $vec#$1_option_Option'$1_optional_aggregator_OptionalAggregator'($supply#$1_coin_CoinInfo'$1_aptos_coin_AptosCoin'($rsc)); (forall $i_2: int :: InRangeVec($range_1, $i_2) ==> (var $elem := ReadVec($range_1, $i_2);
    ((((((($1_option_$is_some'$1_aggregator_Aggregator'($aggregator#$1_optional_aggregator_OptionalAggregator($elem)) <==> $1_option_$is_none'$1_optional_aggregator_Integer'($integer#$1_optional_aggregator_OptionalAggregator($elem))) && ($1_option_$is_some'$1_optional_aggregator_Integer'($integer#$1_optional_aggregator_OptionalAggregator($elem)) <==> $1_option_$is_none'$1_aggregator_Aggregator'($aggregator#$1_optional_aggregator_OptionalAggregator($elem)))) && ($1_option_$is_some'$1_optional_aggregator_Integer'($integer#$1_optional_aggregator_OptionalAggregator($elem)) ==> ($value#$1_optional_aggregator_Integer($1_option_$borrow'$1_optional_aggregator_Integer'($integer#$1_optional_aggregator_OptionalAggregator($elem))) <= $limit#$1_optional_aggregator_Integer($1_option_$borrow'$1_optional_aggregator_Integer'($integer#$1_optional_aggregator_OptionalAggregator($elem)))))) && ($1_option_$is_some'$1_aggregator_Aggregator'($aggregator#$1_optional_aggregator_OptionalAggregator($elem)) ==> ($1_aggregator_spec_aggregator_get_val($1_option_$borrow'$1_aggregator_Aggregator'($aggregator#$1_optional_aggregator_OptionalAggregator($elem))) <= $1_aggregator_spec_get_limit($1_option_$borrow'$1_aggregator_Aggregator'($aggregator#$1_optional_aggregator_OptionalAggregator($elem)))))) && (LenVec($vec#$1_option_Option'$1_aggregator_Aggregator'($aggregator#$1_optional_aggregator_OptionalAggregator($elem))) <= 1)) && (LenVec($vec#$1_option_Option'$1_optional_aggregator_Integer'($integer#$1_optional_aggregator_OptionalAggregator($elem))) <= 1)))))))))));

    // assume forall $rsc: ResourceDomain<coin::Ghost$supply<aptos_coin::AptosCoin>>(): WellFormed($rsc) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:39:5+1
    assume (forall $a_0: int :: {$ResourceValue($1_coin_Ghost$supply'$1_aptos_coin_AptosCoin'_$memory, $a_0)}(var $rsc := $ResourceValue($1_coin_Ghost$supply'$1_aptos_coin_AptosCoin'_$memory, $a_0);
    ($IsValid'$1_coin_Ghost$supply'$1_aptos_coin_AptosCoin''($rsc))));

    // assume exists<coin::Ghost$supply<aptos_coin::AptosCoin>>(0x0) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:39:5+1
    assume $ResourceExists($1_coin_Ghost$supply'$1_aptos_coin_AptosCoin'_$memory, 0);

    // assume forall $rsc: ResourceDomain<coin::Ghost$aggregate_supply<aptos_coin::AptosCoin>>(): WellFormed($rsc) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:39:5+1
    assume (forall $a_0: int :: {$ResourceValue($1_coin_Ghost$aggregate_supply'$1_aptos_coin_AptosCoin'_$memory, $a_0)}(var $rsc := $ResourceValue($1_coin_Ghost$aggregate_supply'$1_aptos_coin_AptosCoin'_$memory, $a_0);
    ($IsValid'$1_coin_Ghost$aggregate_supply'$1_aptos_coin_AptosCoin''($rsc))));

    // assume exists<coin::Ghost$aggregate_supply<aptos_coin::AptosCoin>>(0x0) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:39:5+1
    assume $ResourceExists($1_coin_Ghost$aggregate_supply'$1_aptos_coin_AptosCoin'_$memory, 0);

    // assume forall $rsc: ResourceDomain<aptos_coin::MintCapStore>(): WellFormed($rsc) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:39:5+1
    assume (forall $a_0: int :: {$ResourceValue($1_aptos_coin_MintCapStore_$memory, $a_0)}(var $rsc := $ResourceValue($1_aptos_coin_MintCapStore_$memory, $a_0);
    ($IsValid'$1_aptos_coin_MintCapStore'($rsc))));

    // trace_exp[subauto, at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:10:39+15]($t0) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:10:39+15
    assume {:print "$at(3,272,287)"} true;
    assume {:print "$track_exp_sub(28638):", $t0} true;

    // assume Identical($t4, signer::$address_of($t0)) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:10:20+35
    assume ($t4 == $1_signer_$address_of($t0));

    // trace_exp[subauto, at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:10:20+35]($t4) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:10:20+35
    assume {:print "$track_exp_sub(28639):", $t4} true;

    // assume Identical($t5, signer::$address_of($t0)) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:10:9+47
    assume ($t5 == $1_signer_$address_of($t0));

    // trace_exp[auto, at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:10:9+47]($t5) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:10:9+47
    assume {:print "$track_exp(28640):", $t5} true;

    // trace_global_mem() at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:10:9+47
    assume {:print "$track_global_mem(29112):", $1_aggregator_factory_AggregatorFactory_$memory} true;

    // trace_global_mem() at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:10:9+47
    assume {:print "$track_global_mem(29113):", $1_coin_CoinInfo'$1_aptos_coin_AptosCoin'_$memory} true;

    // trace_global_mem() at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:10:9+47
    assume {:print "$track_global_mem(29114):", $1_coin_Ghost$supply'$1_aptos_coin_AptosCoin'_$memory} true;

    // trace_global_mem() at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:10:9+47
    assume {:print "$track_global_mem(29115):", $1_coin_Ghost$aggregate_supply'$1_aptos_coin_AptosCoin'_$memory} true;

    // trace_global_mem() at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:10:9+47
    assume {:print "$track_global_mem(29116):", $1_aptos_coin_MintCapStore_$memory} true;

    // assume Identical($t6, signer::$address_of($t0)) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:10:9+47
    assume ($t6 == $1_signer_$address_of($t0));

    // trace_exp[subauto, at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:14:70+15]($t0) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:14:70+15
    assume {:print "$at(3,532,547)"} true;
    assume {:print "$track_exp_sub(28644):", $t0} true;

    // assume Identical($t7, signer::$address_of($t0)) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.spec.move:292:28+27
    assume {:print "$at(94,12295,12322)"} true;
    assume ($t7 == $1_signer_$address_of($t0));

    // trace_exp[subauto, at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.spec.move:292:28+27]($t7) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.spec.move:292:28+27
    assume {:print "$track_exp_sub(28645):", $t7} true;

    // assume Identical($t8, signer::$address_of($t0)) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.spec.move:292:9+47
    assume ($t8 == $1_signer_$address_of($t0));

    // trace_exp[auto, at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.spec.move:292:9+47]($t8) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.spec.move:292:9+47
    assume {:print "$track_exp(28646):", $t8} true;

    // trace_global_mem() at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.spec.move:292:9+47
    assume {:print "$track_global_mem(29117):", $1_aggregator_factory_AggregatorFactory_$memory} true;

    // trace_global_mem() at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.spec.move:292:9+47
    assume {:print "$track_global_mem(29118):", $1_coin_CoinInfo'$1_aptos_coin_AptosCoin'_$memory} true;

    // trace_global_mem() at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.spec.move:292:9+47
    assume {:print "$track_global_mem(29119):", $1_coin_Ghost$supply'$1_aptos_coin_AptosCoin'_$memory} true;

    // trace_global_mem() at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.spec.move:292:9+47
    assume {:print "$track_global_mem(29120):", $1_coin_Ghost$aggregate_supply'$1_aptos_coin_AptosCoin'_$memory} true;

    // trace_global_mem() at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.spec.move:292:9+47
    assume {:print "$track_global_mem(29121):", $1_aptos_coin_MintCapStore_$memory} true;

    // assume Identical($t9, signer::$address_of($t0)) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.spec.move:292:9+47
    assume ($t9 == $1_signer_$address_of($t0));

    // assume Identical($t10, type_info::$type_of<aptos_coin::AptosCoin>()) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.spec.move:293:28+30
    assume {:print "$at(94,12351,12381)"} true;
    assume ($t10 == $1_type_info_TypeInfo(1, Vec(DefaultVecMap()[0 := 97][1 := 112][2 := 116][3 := 111][4 := 115][5 := 95][6 := 99][7 := 111][8 := 105][9 := 110], 10), Vec(DefaultVecMap()[0 := 65][1 := 112][2 := 116][3 := 111][4 := 115][5 := 67][6 := 111][7 := 105][8 := 110], 9)));

    // trace_exp[subauto, at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.spec.move:293:28+30]($t10) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.spec.move:293:28+30
    assume {:print "$track_exp_sub(28649):", $t10} true;

    // assume Identical($t11, select type_info::TypeInfo.account_address(type_info::$type_of<aptos_coin::AptosCoin>())) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.spec.move:293:9+66
    assume ($t11 == $account_address#$1_type_info_TypeInfo($1_type_info_TypeInfo(1, Vec(DefaultVecMap()[0 := 97][1 := 112][2 := 116][3 := 111][4 := 115][5 := 95][6 := 99][7 := 111][8 := 105][9 := 110], 10), Vec(DefaultVecMap()[0 := 65][1 := 112][2 := 116][3 := 111][4 := 115][5 := 67][6 := 111][7 := 105][8 := 110], 9))));

    // trace_exp[auto, at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.spec.move:293:9+66]($t11) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.spec.move:293:9+66
    assume {:print "$track_exp(28650):", $t11} true;

    // trace_global_mem() at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.spec.move:293:9+66
    assume {:print "$track_global_mem(29122):", $1_aggregator_factory_AggregatorFactory_$memory} true;

    // trace_global_mem() at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.spec.move:293:9+66
    assume {:print "$track_global_mem(29123):", $1_coin_CoinInfo'$1_aptos_coin_AptosCoin'_$memory} true;

    // trace_global_mem() at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.spec.move:293:9+66
    assume {:print "$track_global_mem(29124):", $1_coin_Ghost$supply'$1_aptos_coin_AptosCoin'_$memory} true;

    // trace_global_mem() at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.spec.move:293:9+66
    assume {:print "$track_global_mem(29125):", $1_coin_Ghost$aggregate_supply'$1_aptos_coin_AptosCoin'_$memory} true;

    // trace_global_mem() at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.spec.move:293:9+66
    assume {:print "$track_global_mem(29126):", $1_aptos_coin_MintCapStore_$memory} true;

    // assume Identical($t12, select type_info::TypeInfo.account_address(type_info::$type_of<aptos_coin::AptosCoin>())) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.spec.move:293:9+66
    assume ($t12 == $account_address#$1_type_info_TypeInfo($1_type_info_TypeInfo(1, Vec(DefaultVecMap()[0 := 97][1 := 112][2 := 116][3 := 111][4 := 115][5 := 95][6 := 99][7 := 111][8 := 105][9 := 110], 10), Vec(DefaultVecMap()[0 := 65][1 := 112][2 := 116][3 := 111][4 := 115][5 := 67][6 := 111][7 := 105][8 := 110], 9))));

    // @28 := save_mem(aggregator_factory::AggregatorFactory) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:39:5+1
    assume {:print "$at(2,1298,1299)"} true;
    $1_aggregator_factory_AggregatorFactory_$memory#28 := $1_aggregator_factory_AggregatorFactory_$memory;

    // @27 := save_mem(coin::CoinInfo<aptos_coin::AptosCoin>) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:39:5+1
    $1_coin_CoinInfo'$1_aptos_coin_AptosCoin'_$memory#27 := $1_coin_CoinInfo'$1_aptos_coin_AptosCoin'_$memory;

    // @29 := save_mem(aptos_coin::MintCapStore) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:39:5+1
    $1_aptos_coin_MintCapStore_$memory#29 := $1_aptos_coin_MintCapStore_$memory;

    // trace_local[aptos_framework]($t0) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:39:5+1
    assume {:print "$track_local(24,6,0):", $t0} $t0 == $t0;

    // opaque begin: system_addresses::assert_aptos_framework($t0) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:40:9+57
    assume {:print "$at(2,1420,1477)"} true;

    // assume Identical($t13, Neq<address>(signer::$address_of($t0), 0x1)) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:40:9+57
    assume ($t13 == !$IsEqual'address'($1_signer_$address_of($t0), 1));

    // if ($t13) goto L4 else goto L3 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:40:9+57
    if ($t13) { goto L4; } else { goto L3; }

    // label L4 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:40:9+57
L4:

    // trace_global_mem() at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:40:9+57
    assume {:print "$at(2,1420,1477)"} true;
    assume {:print "$track_global_mem(29127):", $1_aggregator_factory_AggregatorFactory_$memory} true;

    // trace_global_mem() at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:40:9+57
    assume {:print "$track_global_mem(29128):", $1_coin_CoinInfo'$1_aptos_coin_AptosCoin'_$memory} true;

    // trace_global_mem() at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:40:9+57
    assume {:print "$track_global_mem(29129):", $1_coin_Ghost$supply'$1_aptos_coin_AptosCoin'_$memory} true;

    // trace_global_mem() at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:40:9+57
    assume {:print "$track_global_mem(29130):", $1_coin_Ghost$aggregate_supply'$1_aptos_coin_AptosCoin'_$memory} true;

    // trace_global_mem() at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:40:9+57
    assume {:print "$track_global_mem(29131):", $1_aptos_coin_MintCapStore_$memory} true;

    // assume And(Neq<address>(signer::$address_of($t0), 0x1), Eq(5, $t14)) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:40:9+57
    assume (!$IsEqual'address'($1_signer_$address_of($t0), 1) && $IsEqual'num'(5, $t14));

    // trace_abort($t14) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:40:9+57
    assume {:print "$at(2,1420,1477)"} true;
    assume {:print "$track_abort(24,6):", $t14} $t14 == $t14;

    // goto L2 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:40:9+57
    goto L2;

    // label L3 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:40:9+57
L3:

    // opaque end: system_addresses::assert_aptos_framework($t0) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:40:9+57
    assume {:print "$at(2,1420,1477)"} true;

    // $t15 := [65, 112, 116, 111, 115, 32, 67, 111, 105, 110] at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:44:26+13
    assume {:print "$at(2,1637,1650)"} true;
    $t15 := ConcatVec(ConcatVec(MakeVec4(65, 112, 116, 111), MakeVec4(115, 32, 67, 111)), MakeVec2(105, 110));
    assume $IsValid'vec'u8''($t15);

    // $t16 := string::utf8($t15) on_abort goto L2 with $t14 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:44:13+27
    call $t16 := $1_string_utf8($t15);
    if ($abort_flag) {
        assume {:print "$at(2,1624,1651)"} true;
        $t14 := $abort_code;
        assume {:print "$track_abort(24,6):", $t14} $t14 == $t14;
        goto L2;
    }

    // $t17 := [65, 80, 84] at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:45:26+6
    assume {:print "$at(2,1678,1684)"} true;
    $t17 := MakeVec3(65, 80, 84);
    assume $IsValid'vec'u8''($t17);

    // $t18 := string::utf8($t17) on_abort goto L2 with $t14 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:45:13+20
    call $t18 := $1_string_utf8($t17);
    if ($abort_flag) {
        assume {:print "$at(2,1665,1685)"} true;
        $t14 := $abort_code;
        assume {:print "$track_abort(24,6):", $t14} $t14 == $t14;
        goto L2;
    }

    // $t19 := 8 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:46:13+1
    assume {:print "$at(2,1699,1700)"} true;
    $t19 := 8;
    assume $IsValid'u8'($t19);

    // $t20 := true at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:47:13+4
    assume {:print "$at(2,1726,1730)"} true;
    $t20 := true;
    assume $IsValid'bool'($t20);

    // trace_global_mem() at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:42:48+232
    assume {:print "$at(2,1527,1759)"} true;
    assume {:print "$track_global_mem(29132):", $1_aggregator_factory_AggregatorFactory_$memory} true;

    // trace_global_mem() at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:42:48+232
    assume {:print "$track_global_mem(29133):", $1_coin_CoinInfo'$1_aptos_coin_AptosCoin'_$memory} true;

    // trace_global_mem() at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:42:48+232
    assume {:print "$track_global_mem(29134):", $1_coin_Ghost$supply'$1_aptos_coin_AptosCoin'_$memory} true;

    // trace_global_mem() at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:42:48+232
    assume {:print "$track_global_mem(29135):", $1_coin_Ghost$aggregate_supply'$1_aptos_coin_AptosCoin'_$memory} true;

    // trace_global_mem() at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:42:48+232
    assume {:print "$track_global_mem(29136):", $1_aptos_coin_MintCapStore_$memory} true;

    // assume Identical($t21, signer::$address_of($t0)) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.spec.move:278:9+39
    assume {:print "$at(94,11808,11847)"} true;
    assume ($t21 == $1_signer_$address_of($t0));

    // trace_global_mem() at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.spec.move:278:9+39
    assume {:print "$track_global_mem(29137):", $1_aggregator_factory_AggregatorFactory_$memory} true;

    // trace_global_mem() at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.spec.move:278:9+39
    assume {:print "$track_global_mem(29138):", $1_coin_CoinInfo'$1_aptos_coin_AptosCoin'_$memory} true;

    // trace_global_mem() at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.spec.move:278:9+39
    assume {:print "$track_global_mem(29139):", $1_coin_Ghost$supply'$1_aptos_coin_AptosCoin'_$memory} true;

    // trace_global_mem() at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.spec.move:278:9+39
    assume {:print "$track_global_mem(29140):", $1_coin_Ghost$aggregate_supply'$1_aptos_coin_AptosCoin'_$memory} true;

    // trace_global_mem() at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.spec.move:278:9+39
    assume {:print "$track_global_mem(29141):", $1_aptos_coin_MintCapStore_$memory} true;

    // assume Identical($t22, signer::$address_of($t0)) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.spec.move:292:9+47
    assume {:print "$at(94,12276,12323)"} true;
    assume ($t22 == $1_signer_$address_of($t0));

    // trace_global_mem() at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.spec.move:292:9+47
    assume {:print "$track_global_mem(29142):", $1_aggregator_factory_AggregatorFactory_$memory} true;

    // trace_global_mem() at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.spec.move:292:9+47
    assume {:print "$track_global_mem(29143):", $1_coin_CoinInfo'$1_aptos_coin_AptosCoin'_$memory} true;

    // trace_global_mem() at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.spec.move:292:9+47
    assume {:print "$track_global_mem(29144):", $1_coin_Ghost$supply'$1_aptos_coin_AptosCoin'_$memory} true;

    // trace_global_mem() at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.spec.move:292:9+47
    assume {:print "$track_global_mem(29145):", $1_coin_Ghost$aggregate_supply'$1_aptos_coin_AptosCoin'_$memory} true;

    // trace_global_mem() at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.spec.move:292:9+47
    assume {:print "$track_global_mem(29146):", $1_aptos_coin_MintCapStore_$memory} true;

    // assume Identical($t23, select type_info::TypeInfo.account_address(type_info::$type_of<aptos_coin::AptosCoin>())) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.spec.move:293:9+66
    assume {:print "$at(94,12332,12398)"} true;
    assume ($t23 == $account_address#$1_type_info_TypeInfo($1_type_info_TypeInfo(1, Vec(DefaultVecMap()[0 := 97][1 := 112][2 := 116][3 := 111][4 := 115][5 := 95][6 := 99][7 := 111][8 := 105][9 := 110], 10), Vec(DefaultVecMap()[0 := 65][1 := 112][2 := 116][3 := 111][4 := 115][5 := 67][6 := 111][7 := 105][8 := 110], 9))));

    // ($t24, $t25, $t26) := coin::initialize_with_parallelizable_supply<aptos_coin::AptosCoin>($t0, $t16, $t18, $t19, $t20) on_abort goto L2 with $t14 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:42:48+232
    assume {:print "$at(2,1527,1759)"} true;
    call $t24,$t25,$t26 := $1_coin_initialize_with_parallelizable_supply'$1_aptos_coin_AptosCoin'($t0, $t16, $t18, $t19, $t20);
    if ($abort_flag) {
        assume {:print "$at(2,1527,1759)"} true;
        $t14 := $abort_code;
        assume {:print "$track_abort(24,6):", $t14} $t14 == $t14;
        goto L2;
    }

    // trace_local[mint_cap]($t26) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:42:36+8
    assume {:print "$track_local(24,6,3):", $t26} $t26 == $t26;

    // trace_local[freeze_cap]($t25) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:42:24+10
    assume {:print "$track_local(24,6,2):", $t25} $t25 == $t25;

    // trace_local[burn_cap]($t24) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:42:14+8
    assume {:print "$track_local(24,6,1):", $t24} $t24 == $t24;

    // $t27 := pack aptos_coin::MintCapStore($t26) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:52:34+25
    assume {:print "$at(2,1949,1974)"} true;
    $t27 := $1_aptos_coin_MintCapStore($t26);

    // move_to<aptos_coin::MintCapStore>($t27, $t0) on_abort goto L2 with $t14 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:52:9+7
    if ($ResourceExists($1_aptos_coin_MintCapStore_$memory, $addr#$signer($t0))) {
        call $ExecFailureAbort();
    } else {
        $1_aptos_coin_MintCapStore_$memory := $ResourceUpdate($1_aptos_coin_MintCapStore_$memory, $addr#$signer($t0), $t27);
    }
    if ($abort_flag) {
        assume {:print "$at(2,1924,1931)"} true;
        $t14 := $abort_code;
        assume {:print "$track_abort(24,6):", $t14} $t14 == $t14;
        goto L2;
    }

    // trace_global_mem() at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:54:9+36
    assume {:print "$at(2,1986,2022)"} true;
    assume {:print "$track_global_mem(29147):", $1_aggregator_factory_AggregatorFactory_$memory} true;

    // trace_global_mem() at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:54:9+36
    assume {:print "$track_global_mem(29148):", $1_coin_CoinInfo'$1_aptos_coin_AptosCoin'_$memory} true;

    // trace_global_mem() at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:54:9+36
    assume {:print "$track_global_mem(29149):", $1_coin_Ghost$supply'$1_aptos_coin_AptosCoin'_$memory} true;

    // trace_global_mem() at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:54:9+36
    assume {:print "$track_global_mem(29150):", $1_coin_Ghost$aggregate_supply'$1_aptos_coin_AptosCoin'_$memory} true;

    // trace_global_mem() at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:54:9+36
    assume {:print "$track_global_mem(29151):", $1_aptos_coin_MintCapStore_$memory} true;

    // assume Identical($t28, select coin::CoinInfo.supply(global<coin::CoinInfo<aptos_coin::AptosCoin>>(select type_info::TypeInfo.account_address(type_info::$type_of<aptos_coin::AptosCoin>())))) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.spec.move:32:9+99
    assume {:print "$at(94,1664,1763)"} true;
    assume ($t28 == $supply#$1_coin_CoinInfo'$1_aptos_coin_AptosCoin'($ResourceValue($1_coin_CoinInfo'$1_aptos_coin_AptosCoin'_$memory, $account_address#$1_type_info_TypeInfo($1_type_info_TypeInfo(1, Vec(DefaultVecMap()[0 := 97][1 := 112][2 := 116][3 := 111][4 := 115][5 := 95][6 := 99][7 := 111][8 := 105][9 := 110], 10), Vec(DefaultVecMap()[0 := 65][1 := 112][2 := 116][3 := 111][4 := 115][5 := 67][6 := 111][7 := 105][8 := 110], 9))))));

    // coin::destroy_freeze_cap<aptos_coin::AptosCoin>($t25) on_abort goto L2 with $t14 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:54:9+36
    assume {:print "$at(2,1986,2022)"} true;
    call $1_coin_destroy_freeze_cap'$1_aptos_coin_AptosCoin'($t25);
    if ($abort_flag) {
        assume {:print "$at(2,1986,2022)"} true;
        $t14 := $abort_code;
        assume {:print "$track_abort(24,6):", $t14} $t14 == $t14;
        goto L2;
    }

    // trace_return[0]($t24) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:55:9+20
    assume {:print "$at(2,2032,2052)"} true;
    assume {:print "$track_return(24,6,0):", $t24} $t24 == $t24;

    // trace_return[1]($t26) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:55:9+20
    assume {:print "$track_return(24,6,1):", $t26} $t26 == $t26;

    // label L1 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:56:5+1
    assume {:print "$at(2,2057,2058)"} true;
L1:

    // trace_exp[subauto, at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:11:19+4]($t6) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:11:19+4
    assume {:print "$at(3,308,312)"} true;
    assume {:print "$track_exp_sub(28654):", $t6} true;

    // assume Identical($t29, Neq<address>($t6, 0x1)) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:11:9+35
    assume ($t29 == !$IsEqual'address'($t6, 1));

    // trace_exp[auto, at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:11:9+35]($t29) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:11:9+35
    assume {:print "$track_exp(28655):", $t29} true;

    // trace_global_mem() at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:11:9+35
    assume {:print "$track_global_mem(29152):", $1_aggregator_factory_AggregatorFactory_$memory} true;

    // trace_global_mem() at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:11:9+35
    assume {:print "$track_global_mem(29153):", $1_coin_CoinInfo'$1_aptos_coin_AptosCoin'_$memory} true;

    // trace_global_mem() at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:11:9+35
    assume {:print "$track_global_mem(29154):", $1_coin_Ghost$supply'$1_aptos_coin_AptosCoin'_$memory} true;

    // trace_global_mem() at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:11:9+35
    assume {:print "$track_global_mem(29155):", $1_coin_Ghost$aggregate_supply'$1_aptos_coin_AptosCoin'_$memory} true;

    // trace_global_mem() at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:11:9+35
    assume {:print "$track_global_mem(29156):", $1_aptos_coin_MintCapStore_$memory} true;

    // assert Not(Neq<address>($t6, 0x1)) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:11:9+35
    assert {:msg "assert_failed(3,298,333): function does not abort under this condition"}
      !!$IsEqual'address'($t6, 1);

    // assume Identical($t30, string::spec_internal_check_utf8[]([65, 112, 116, 111, 115, 32, 67, 111, 105, 110])) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:12:20+47
    assume {:print "$at(3,353,400)"} true;
    assume ($t30 == $1_string_spec_internal_check_utf8(ConcatVec(ConcatVec(MakeVec4(65, 112, 116, 111), MakeVec4(115, 32, 67, 111)), MakeVec2(105, 110))));

    // trace_exp[subauto, at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:12:20+47]($t30) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:12:20+47
    assume {:print "$track_exp_sub(28658):", $t30} true;

    // assume Identical($t31, Not(string::spec_internal_check_utf8[]([65, 112, 116, 111, 115, 32, 67, 111, 105, 110]))) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:12:9+59
    assume ($t31 == !$1_string_spec_internal_check_utf8(ConcatVec(ConcatVec(MakeVec4(65, 112, 116, 111), MakeVec4(115, 32, 67, 111)), MakeVec2(105, 110))));

    // trace_exp[auto, at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:12:9+59]($t31) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:12:9+59
    assume {:print "$track_exp(28659):", $t31} true;

    // trace_global_mem() at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:12:9+59
    assume {:print "$track_global_mem(29157):", $1_aggregator_factory_AggregatorFactory_$memory} true;

    // trace_global_mem() at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:12:9+59
    assume {:print "$track_global_mem(29158):", $1_coin_CoinInfo'$1_aptos_coin_AptosCoin'_$memory} true;

    // trace_global_mem() at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:12:9+59
    assume {:print "$track_global_mem(29159):", $1_coin_Ghost$supply'$1_aptos_coin_AptosCoin'_$memory} true;

    // trace_global_mem() at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:12:9+59
    assume {:print "$track_global_mem(29160):", $1_coin_Ghost$aggregate_supply'$1_aptos_coin_AptosCoin'_$memory} true;

    // trace_global_mem() at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:12:9+59
    assume {:print "$track_global_mem(29161):", $1_aptos_coin_MintCapStore_$memory} true;

    // assert Not(Not(string::spec_internal_check_utf8[]([65, 112, 116, 111, 115, 32, 67, 111, 105, 110]))) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:12:9+59
    assert {:msg "assert_failed(3,342,401): function does not abort under this condition"}
      !!$1_string_spec_internal_check_utf8(ConcatVec(ConcatVec(MakeVec4(65, 112, 116, 111), MakeVec4(115, 32, 67, 111)), MakeVec2(105, 110)));

    // assume Identical($t32, string::spec_internal_check_utf8[]([65, 80, 84])) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:13:20+40
    assume {:print "$at(3,421,461)"} true;
    assume ($t32 == $1_string_spec_internal_check_utf8(MakeVec3(65, 80, 84)));

    // trace_exp[subauto, at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:13:20+40]($t32) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:13:20+40
    assume {:print "$track_exp_sub(28662):", $t32} true;

    // assume Identical($t33, Not(string::spec_internal_check_utf8[]([65, 80, 84]))) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:13:9+52
    assume ($t33 == !$1_string_spec_internal_check_utf8(MakeVec3(65, 80, 84)));

    // trace_exp[auto, at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:13:9+52]($t33) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:13:9+52
    assume {:print "$track_exp(28663):", $t33} true;

    // trace_global_mem() at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:13:9+52
    assume {:print "$track_global_mem(29162):", $1_aggregator_factory_AggregatorFactory_$memory} true;

    // trace_global_mem() at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:13:9+52
    assume {:print "$track_global_mem(29163):", $1_coin_CoinInfo'$1_aptos_coin_AptosCoin'_$memory} true;

    // trace_global_mem() at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:13:9+52
    assume {:print "$track_global_mem(29164):", $1_coin_Ghost$supply'$1_aptos_coin_AptosCoin'_$memory} true;

    // trace_global_mem() at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:13:9+52
    assume {:print "$track_global_mem(29165):", $1_coin_Ghost$aggregate_supply'$1_aptos_coin_AptosCoin'_$memory} true;

    // trace_global_mem() at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:13:9+52
    assume {:print "$track_global_mem(29166):", $1_aptos_coin_MintCapStore_$memory} true;

    // assert Not(Not(string::spec_internal_check_utf8[]([65, 80, 84]))) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:13:9+52
    assert {:msg "assert_failed(3,410,462): function does not abort under this condition"}
      !!$1_string_spec_internal_check_utf8(MakeVec3(65, 80, 84));

    // trace_exp[subauto, at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.spec.move:294:19+12]($t12) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.spec.move:294:19+12
    assume {:print "$at(94,12417,12429)"} true;
    assume {:print "$track_exp_sub(28668):", $t12} true;

    // trace_exp[subauto, at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.spec.move:294:35+12]($t9) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.spec.move:294:35+12
    assume {:print "$track_exp_sub(28670):", $t9} true;

    // assume Identical($t34, Neq<address>($t12, $t9)) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.spec.move:294:9+39
    assume ($t34 == !$IsEqual'address'($t12, $t9));

    // trace_exp[auto, at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.spec.move:294:9+39]($t34) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.spec.move:294:9+39
    assume {:print "$track_exp(28671):", $t34} true;

    // trace_global_mem() at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.spec.move:294:9+39
    assume {:print "$track_global_mem(29167):", $1_aggregator_factory_AggregatorFactory_$memory} true;

    // trace_global_mem() at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.spec.move:294:9+39
    assume {:print "$track_global_mem(29168):", $1_coin_CoinInfo'$1_aptos_coin_AptosCoin'_$memory} true;

    // trace_global_mem() at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.spec.move:294:9+39
    assume {:print "$track_global_mem(29169):", $1_coin_Ghost$supply'$1_aptos_coin_AptosCoin'_$memory} true;

    // trace_global_mem() at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.spec.move:294:9+39
    assume {:print "$track_global_mem(29170):", $1_coin_Ghost$aggregate_supply'$1_aptos_coin_AptosCoin'_$memory} true;

    // trace_global_mem() at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.spec.move:294:9+39
    assume {:print "$track_global_mem(29171):", $1_aptos_coin_MintCapStore_$memory} true;

    // assert Not(Neq<address>($t12, $t9)) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.spec.move:294:9+39
    assert {:msg "assert_failed(94,12407,12446): function does not abort under this condition"}
      !!$IsEqual'address'($t12, $t9);

    // trace_exp[subauto, at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.spec.move:295:46+12]($t9) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.spec.move:295:46+12
    assume {:print "$at(94,12492,12504)"} true;
    assume {:print "$track_exp_sub(28676):", $t9} true;

    // assume Identical($t35, exists[@27]<coin::CoinInfo<aptos_coin::AptosCoin>>($t9)) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.spec.move:295:19+40
    assume ($t35 == $ResourceExists($1_coin_CoinInfo'$1_aptos_coin_AptosCoin'_$memory#27, $t9));

    // trace_exp[subauto, at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.spec.move:295:19+40]($t35) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.spec.move:295:19+40
    assume {:print "$track_exp_sub(28677):", $t35} true;

    // assume Identical($t36, exists[@27]<coin::CoinInfo<aptos_coin::AptosCoin>>($t9)) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.spec.move:295:9+51
    assume ($t36 == $ResourceExists($1_coin_CoinInfo'$1_aptos_coin_AptosCoin'_$memory#27, $t9));

    // trace_exp[auto, at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.spec.move:295:9+51]($t36) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.spec.move:295:9+51
    assume {:print "$track_exp(28678):", $t36} true;

    // trace_global_mem() at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.spec.move:295:9+51
    assume {:print "$track_global_mem(29172):", $1_aggregator_factory_AggregatorFactory_$memory} true;

    // trace_global_mem() at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.spec.move:295:9+51
    assume {:print "$track_global_mem(29173):", $1_coin_CoinInfo'$1_aptos_coin_AptosCoin'_$memory} true;

    // trace_global_mem() at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.spec.move:295:9+51
    assume {:print "$track_global_mem(29174):", $1_coin_Ghost$supply'$1_aptos_coin_AptosCoin'_$memory} true;

    // trace_global_mem() at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.spec.move:295:9+51
    assume {:print "$track_global_mem(29175):", $1_coin_Ghost$aggregate_supply'$1_aptos_coin_AptosCoin'_$memory} true;

    // trace_global_mem() at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.spec.move:295:9+51
    assume {:print "$track_global_mem(29176):", $1_aptos_coin_MintCapStore_$memory} true;

    // assert Not(exists[@27]<coin::CoinInfo<aptos_coin::AptosCoin>>($t9)) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.spec.move:295:9+51
    assert {:msg "assert_failed(94,12455,12506): function does not abort under this condition"}
      !$ResourceExists($1_coin_CoinInfo'$1_aptos_coin_AptosCoin'_$memory#27, $t9);

    // assume Identical($t37, Gt(Len<u8>([65, 112, 116, 111, 115, 32, 67, 111, 105, 110]), 32)) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.spec.move:296:9+43
    assume {:print "$at(94,12515,12558)"} true;
    assume ($t37 == (LenVec(ConcatVec(ConcatVec(MakeVec4(65, 112, 116, 111), MakeVec4(115, 32, 67, 111)), MakeVec2(105, 110))) > 32));

    // trace_exp[auto, at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.spec.move:296:9+43]($t37) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.spec.move:296:9+43
    assume {:print "$track_exp(28680):", $t37} true;

    // trace_global_mem() at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.spec.move:296:9+43
    assume {:print "$track_global_mem(29177):", $1_aggregator_factory_AggregatorFactory_$memory} true;

    // trace_global_mem() at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.spec.move:296:9+43
    assume {:print "$track_global_mem(29178):", $1_coin_CoinInfo'$1_aptos_coin_AptosCoin'_$memory} true;

    // trace_global_mem() at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.spec.move:296:9+43
    assume {:print "$track_global_mem(29179):", $1_coin_Ghost$supply'$1_aptos_coin_AptosCoin'_$memory} true;

    // trace_global_mem() at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.spec.move:296:9+43
    assume {:print "$track_global_mem(29180):", $1_coin_Ghost$aggregate_supply'$1_aptos_coin_AptosCoin'_$memory} true;

    // trace_global_mem() at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.spec.move:296:9+43
    assume {:print "$track_global_mem(29181):", $1_aptos_coin_MintCapStore_$memory} true;

    // assert Not(Gt(Len<u8>([65, 112, 116, 111, 115, 32, 67, 111, 105, 110]), 32)) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.spec.move:296:9+43
    assert {:msg "assert_failed(94,12515,12558): function does not abort under this condition"}
      !(LenVec(ConcatVec(ConcatVec(MakeVec4(65, 112, 116, 111), MakeVec4(115, 32, 67, 111)), MakeVec2(105, 110))) > 32);

    // assume Identical($t38, Gt(Len<u8>([65, 80, 84]), 10)) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.spec.move:297:9+47
    assume {:print "$at(94,12567,12614)"} true;
    assume ($t38 == (LenVec(MakeVec3(65, 80, 84)) > 10));

    // trace_exp[auto, at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.spec.move:297:9+47]($t38) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.spec.move:297:9+47
    assume {:print "$track_exp(28682):", $t38} true;

    // trace_global_mem() at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.spec.move:297:9+47
    assume {:print "$track_global_mem(29182):", $1_aggregator_factory_AggregatorFactory_$memory} true;

    // trace_global_mem() at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.spec.move:297:9+47
    assume {:print "$track_global_mem(29183):", $1_coin_CoinInfo'$1_aptos_coin_AptosCoin'_$memory} true;

    // trace_global_mem() at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.spec.move:297:9+47
    assume {:print "$track_global_mem(29184):", $1_coin_Ghost$supply'$1_aptos_coin_AptosCoin'_$memory} true;

    // trace_global_mem() at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.spec.move:297:9+47
    assume {:print "$track_global_mem(29185):", $1_coin_Ghost$aggregate_supply'$1_aptos_coin_AptosCoin'_$memory} true;

    // trace_global_mem() at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.spec.move:297:9+47
    assume {:print "$track_global_mem(29186):", $1_aptos_coin_MintCapStore_$memory} true;

    // assert Not(Gt(Len<u8>([65, 80, 84]), 10)) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.spec.move:297:9+47
    assert {:msg "assert_failed(94,12567,12614): function does not abort under this condition"}
      !(LenVec(MakeVec3(65, 80, 84)) > 10);

    // assume Identical($t39, exists[@28]<aggregator_factory::AggregatorFactory>(0x1)) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:15:20+80
    assume {:print "$at(3,607,687)"} true;
    assume ($t39 == $ResourceExists($1_aggregator_factory_AggregatorFactory_$memory#28, 1));

    // trace_exp[subauto, at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:15:20+80]($t39) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:15:20+80
    assume {:print "$track_exp_sub(28685):", $t39} true;

    // assume Identical($t40, Not(exists[@28]<aggregator_factory::AggregatorFactory>(0x1))) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:15:9+92
    assume ($t40 == !$ResourceExists($1_aggregator_factory_AggregatorFactory_$memory#28, 1));

    // trace_exp[auto, at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:15:9+92]($t40) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:15:9+92
    assume {:print "$track_exp(28686):", $t40} true;

    // trace_global_mem() at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:15:9+92
    assume {:print "$track_global_mem(29187):", $1_aggregator_factory_AggregatorFactory_$memory} true;

    // trace_global_mem() at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:15:9+92
    assume {:print "$track_global_mem(29188):", $1_coin_CoinInfo'$1_aptos_coin_AptosCoin'_$memory} true;

    // trace_global_mem() at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:15:9+92
    assume {:print "$track_global_mem(29189):", $1_coin_Ghost$supply'$1_aptos_coin_AptosCoin'_$memory} true;

    // trace_global_mem() at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:15:9+92
    assume {:print "$track_global_mem(29190):", $1_coin_Ghost$aggregate_supply'$1_aptos_coin_AptosCoin'_$memory} true;

    // trace_global_mem() at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:15:9+92
    assume {:print "$track_global_mem(29191):", $1_aptos_coin_MintCapStore_$memory} true;

    // assert Not(Not(exists[@28]<aggregator_factory::AggregatorFactory>(0x1))) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:15:9+92
    assert {:msg "assert_failed(3,596,688): function does not abort under this condition"}
      !!$ResourceExists($1_aggregator_factory_AggregatorFactory_$memory#28, 1);

    // trace_exp[subauto, at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:16:40+4]($t6) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:16:40+4
    assume {:print "$at(3,728,732)"} true;
    assume {:print "$track_exp_sub(28691):", $t6} true;

    // assume Identical($t41, exists[@29]<aptos_coin::MintCapStore>($t6)) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:16:19+26
    assume ($t41 == $ResourceExists($1_aptos_coin_MintCapStore_$memory#29, $t6));

    // trace_exp[subauto, at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:16:19+26]($t41) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:16:19+26
    assume {:print "$track_exp_sub(28692):", $t41} true;

    // assume Identical($t42, exists[@29]<aptos_coin::MintCapStore>($t6)) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:16:9+37
    assume ($t42 == $ResourceExists($1_aptos_coin_MintCapStore_$memory#29, $t6));

    // trace_exp[auto, at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:16:9+37]($t42) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:16:9+37
    assume {:print "$track_exp(28693):", $t42} true;

    // trace_global_mem() at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:16:9+37
    assume {:print "$track_global_mem(29192):", $1_aggregator_factory_AggregatorFactory_$memory} true;

    // trace_global_mem() at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:16:9+37
    assume {:print "$track_global_mem(29193):", $1_coin_CoinInfo'$1_aptos_coin_AptosCoin'_$memory} true;

    // trace_global_mem() at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:16:9+37
    assume {:print "$track_global_mem(29194):", $1_coin_Ghost$supply'$1_aptos_coin_AptosCoin'_$memory} true;

    // trace_global_mem() at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:16:9+37
    assume {:print "$track_global_mem(29195):", $1_coin_Ghost$aggregate_supply'$1_aptos_coin_AptosCoin'_$memory} true;

    // trace_global_mem() at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:16:9+37
    assume {:print "$track_global_mem(29196):", $1_aptos_coin_MintCapStore_$memory} true;

    // assert Not(exists[@29]<aptos_coin::MintCapStore>($t6)) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:16:9+37
    assert {:msg "assert_failed(3,697,734): function does not abort under this condition"}
      !$ResourceExists($1_aptos_coin_MintCapStore_$memory#29, $t6);

    // trace_exp[subauto, at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:18:38+4]($t6) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:18:38+4
    assume {:print "$at(3,773,777)"} true;
    assume {:print "$track_exp_sub(28698):", $t6} true;

    // assume Identical($t43, exists<aptos_coin::MintCapStore>($t6)) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:18:17+26
    assume ($t43 == $ResourceExists($1_aptos_coin_MintCapStore_$memory, $t6));

    // trace_exp[subauto, at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:18:17+26]($t43) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:18:17+26
    assume {:print "$track_exp_sub(28699):", $t43} true;

    // assume Identical($t44, exists<aptos_coin::MintCapStore>($t6)) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:18:9+35
    assume ($t44 == $ResourceExists($1_aptos_coin_MintCapStore_$memory, $t6));

    // trace_exp[auto, at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:18:9+35]($t44) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:18:9+35
    assume {:print "$track_exp(28700):", $t44} true;

    // trace_global_mem() at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:18:9+35
    assume {:print "$track_global_mem(29197):", $1_aggregator_factory_AggregatorFactory_$memory} true;

    // trace_global_mem() at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:18:9+35
    assume {:print "$track_global_mem(29198):", $1_coin_CoinInfo'$1_aptos_coin_AptosCoin'_$memory} true;

    // trace_global_mem() at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:18:9+35
    assume {:print "$track_global_mem(29199):", $1_coin_Ghost$supply'$1_aptos_coin_AptosCoin'_$memory} true;

    // trace_global_mem() at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:18:9+35
    assume {:print "$track_global_mem(29200):", $1_coin_Ghost$aggregate_supply'$1_aptos_coin_AptosCoin'_$memory} true;

    // trace_global_mem() at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:18:9+35
    assume {:print "$track_global_mem(29201):", $1_aptos_coin_MintCapStore_$memory} true;

    // assert exists<aptos_coin::MintCapStore>($t6) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:18:9+35
    assert {:msg "assert_failed(3,744,779): post-condition does not hold"}
      $ResourceExists($1_aptos_coin_MintCapStore_$memory, $t6);

    // trace_exp[subauto, at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:19:51+4]($t6) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:19:51+4
    assume {:print "$at(3,830,834)"} true;
    assume {:print "$track_exp_sub(28705):", $t6} true;

    // assume Identical($t45, exists<coin::CoinInfo<aptos_coin::AptosCoin>>($t6)) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:19:17+39
    assume ($t45 == $ResourceExists($1_coin_CoinInfo'$1_aptos_coin_AptosCoin'_$memory, $t6));

    // trace_exp[subauto, at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:19:17+39]($t45) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:19:17+39
    assume {:print "$track_exp_sub(28706):", $t45} true;

    // assume Identical($t46, exists<coin::CoinInfo<aptos_coin::AptosCoin>>($t6)) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:19:9+48
    assume ($t46 == $ResourceExists($1_coin_CoinInfo'$1_aptos_coin_AptosCoin'_$memory, $t6));

    // trace_exp[auto, at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:19:9+48]($t46) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:19:9+48
    assume {:print "$track_exp(28707):", $t46} true;

    // trace_global_mem() at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:19:9+48
    assume {:print "$track_global_mem(29202):", $1_aggregator_factory_AggregatorFactory_$memory} true;

    // trace_global_mem() at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:19:9+48
    assume {:print "$track_global_mem(29203):", $1_coin_CoinInfo'$1_aptos_coin_AptosCoin'_$memory} true;

    // trace_global_mem() at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:19:9+48
    assume {:print "$track_global_mem(29204):", $1_coin_Ghost$supply'$1_aptos_coin_AptosCoin'_$memory} true;

    // trace_global_mem() at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:19:9+48
    assume {:print "$track_global_mem(29205):", $1_coin_Ghost$aggregate_supply'$1_aptos_coin_AptosCoin'_$memory} true;

    // trace_global_mem() at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:19:9+48
    assume {:print "$track_global_mem(29206):", $1_aptos_coin_MintCapStore_$memory} true;

    // assert exists<coin::CoinInfo<aptos_coin::AptosCoin>>($t6) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:19:9+48
    assert {:msg "assert_failed(3,788,836): post-condition does not hold"}
      $ResourceExists($1_coin_CoinInfo'$1_aptos_coin_AptosCoin'_$memory, $t6);

    // trace_exp[subauto, at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:20:97+4]($t6) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:20:97+4
    assume {:print "$at(3,933,937)"} true;
    assume {:print "$track_exp_sub(28714):", $t6} true;

    // assume Identical($t47, global<coin::CoinInfo<aptos_coin::AptosCoin>>($t6)) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:20:63+39
    assume ($t47 == $ResourceValue($1_coin_CoinInfo'$1_aptos_coin_AptosCoin'_$memory, $t6));

    // trace_exp[subauto, at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:20:63+39]($t47) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:20:63+39
    assume {:print "$track_exp_sub(28715):", $t47} true;

    // assume Identical($t48, option::spec_borrow<optional_aggregator::OptionalAggregator>(select coin::CoinInfo.supply(global<coin::CoinInfo<aptos_coin::AptosCoin>>($t6)))) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:20:43+67
    assume ($t48 == $1_option_spec_borrow'$1_optional_aggregator_OptionalAggregator'($supply#$1_coin_CoinInfo'$1_aptos_coin_AptosCoin'($ResourceValue($1_coin_CoinInfo'$1_aptos_coin_AptosCoin'_$memory, $t6))));

    // trace_exp[subauto, at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:20:43+67]($t48) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:20:43+67
    assume {:print "$track_exp_sub(28716):", $t48} true;

    // assume Identical($t49, optional_aggregator::optional_aggregator_value(option::spec_borrow<optional_aggregator::OptionalAggregator>(select coin::CoinInfo.supply(global<coin::CoinInfo<aptos_coin::AptosCoin>>($t6))))) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:20:17+94
    assume ($t49 == $1_optional_aggregator_optional_aggregator_value($1_option_spec_borrow'$1_optional_aggregator_OptionalAggregator'($supply#$1_coin_CoinInfo'$1_aptos_coin_AptosCoin'($ResourceValue($1_coin_CoinInfo'$1_aptos_coin_AptosCoin'_$memory, $t6)))));

    // trace_exp[subauto, at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:20:17+94]($t49) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:20:17+94
    assume {:print "$track_exp_sub(28717):", $t49} true;

    // assume Identical($t50, Eq<u128>(optional_aggregator::optional_aggregator_value(option::spec_borrow<optional_aggregator::OptionalAggregator>(select coin::CoinInfo.supply(global<coin::CoinInfo<aptos_coin::AptosCoin>>($t6)))), 0)) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:20:9+108
    assume ($t50 == $IsEqual'u128'($1_optional_aggregator_optional_aggregator_value($1_option_spec_borrow'$1_optional_aggregator_OptionalAggregator'($supply#$1_coin_CoinInfo'$1_aptos_coin_AptosCoin'($ResourceValue($1_coin_CoinInfo'$1_aptos_coin_AptosCoin'_$memory, $t6)))), 0));

    // trace_exp[auto, at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:20:9+108]($t50) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:20:9+108
    assume {:print "$track_exp(28718):", $t50} true;

    // trace_global_mem() at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:20:9+108
    assume {:print "$track_global_mem(29207):", $1_aggregator_factory_AggregatorFactory_$memory} true;

    // trace_global_mem() at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:20:9+108
    assume {:print "$track_global_mem(29208):", $1_coin_CoinInfo'$1_aptos_coin_AptosCoin'_$memory} true;

    // trace_global_mem() at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:20:9+108
    assume {:print "$track_global_mem(29209):", $1_coin_Ghost$supply'$1_aptos_coin_AptosCoin'_$memory} true;

    // trace_global_mem() at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:20:9+108
    assume {:print "$track_global_mem(29210):", $1_coin_Ghost$aggregate_supply'$1_aptos_coin_AptosCoin'_$memory} true;

    // trace_global_mem() at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:20:9+108
    assume {:print "$track_global_mem(29211):", $1_aptos_coin_MintCapStore_$memory} true;

    // assert Eq<u128>(optional_aggregator::optional_aggregator_value(option::spec_borrow<optional_aggregator::OptionalAggregator>(select coin::CoinInfo.supply(global<coin::CoinInfo<aptos_coin::AptosCoin>>($t6)))), 0) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:20:9+108
    assert {:msg "assert_failed(3,845,953): post-condition does not hold"}
      $IsEqual'u128'($1_optional_aggregator_optional_aggregator_value($1_option_spec_borrow'$1_optional_aggregator_OptionalAggregator'($supply#$1_coin_CoinInfo'$1_aptos_coin_AptosCoin'($ResourceValue($1_coin_CoinInfo'$1_aptos_coin_AptosCoin'_$memory, $t6)))), 0);

    // trace_exp[subauto, at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:21:17+8]($t24) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:21:17+8
    assume {:print "$at(3,970,978)"} true;
    assume {:print "$track_exp_sub(28722):", $t24} true;

    // assume Identical($t51, Eq<coin::BurnCapability<aptos_coin::AptosCoin>>($t24, pack coin::BurnCapability<aptos_coin::AptosCoin>(false))) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:21:9+48
    assume ($t51 == $IsEqual'$1_coin_BurnCapability'$1_aptos_coin_AptosCoin''($t24, $1_coin_BurnCapability'$1_aptos_coin_AptosCoin'(false)));

    // trace_exp[auto, at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:21:9+48]($t51) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:21:9+48
    assume {:print "$track_exp(28723):", $t51} true;

    // trace_global_mem() at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:21:9+48
    assume {:print "$track_global_mem(29212):", $1_aggregator_factory_AggregatorFactory_$memory} true;

    // trace_global_mem() at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:21:9+48
    assume {:print "$track_global_mem(29213):", $1_coin_CoinInfo'$1_aptos_coin_AptosCoin'_$memory} true;

    // trace_global_mem() at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:21:9+48
    assume {:print "$track_global_mem(29214):", $1_coin_Ghost$supply'$1_aptos_coin_AptosCoin'_$memory} true;

    // trace_global_mem() at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:21:9+48
    assume {:print "$track_global_mem(29215):", $1_coin_Ghost$aggregate_supply'$1_aptos_coin_AptosCoin'_$memory} true;

    // trace_global_mem() at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:21:9+48
    assume {:print "$track_global_mem(29216):", $1_aptos_coin_MintCapStore_$memory} true;

    // assert Eq<coin::BurnCapability<aptos_coin::AptosCoin>>($t24, pack coin::BurnCapability<aptos_coin::AptosCoin>(false)) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:21:9+48
    assert {:msg "assert_failed(3,962,1010): post-condition does not hold"}
      $IsEqual'$1_coin_BurnCapability'$1_aptos_coin_AptosCoin''($t24, $1_coin_BurnCapability'$1_aptos_coin_AptosCoin'(false));

    // trace_exp[subauto, at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:22:17+8]($t26) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:22:17+8
    assume {:print "$at(3,1027,1035)"} true;
    assume {:print "$track_exp_sub(28727):", $t26} true;

    // assume Identical($t52, Eq<coin::MintCapability<aptos_coin::AptosCoin>>($t26, pack coin::MintCapability<aptos_coin::AptosCoin>(false))) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:22:9+48
    assume ($t52 == $IsEqual'$1_coin_MintCapability'$1_aptos_coin_AptosCoin''($t26, $1_coin_MintCapability'$1_aptos_coin_AptosCoin'(false)));

    // trace_exp[auto, at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:22:9+48]($t52) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:22:9+48
    assume {:print "$track_exp(28728):", $t52} true;

    // trace_global_mem() at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:22:9+48
    assume {:print "$track_global_mem(29217):", $1_aggregator_factory_AggregatorFactory_$memory} true;

    // trace_global_mem() at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:22:9+48
    assume {:print "$track_global_mem(29218):", $1_coin_CoinInfo'$1_aptos_coin_AptosCoin'_$memory} true;

    // trace_global_mem() at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:22:9+48
    assume {:print "$track_global_mem(29219):", $1_coin_Ghost$supply'$1_aptos_coin_AptosCoin'_$memory} true;

    // trace_global_mem() at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:22:9+48
    assume {:print "$track_global_mem(29220):", $1_coin_Ghost$aggregate_supply'$1_aptos_coin_AptosCoin'_$memory} true;

    // trace_global_mem() at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:22:9+48
    assume {:print "$track_global_mem(29221):", $1_aptos_coin_MintCapStore_$memory} true;

    // assert Eq<coin::MintCapability<aptos_coin::AptosCoin>>($t26, pack coin::MintCapability<aptos_coin::AptosCoin>(false)) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:22:9+48
    assert {:msg "assert_failed(3,1019,1067): post-condition does not hold"}
      $IsEqual'$1_coin_MintCapability'$1_aptos_coin_AptosCoin''($t26, $1_coin_MintCapability'$1_aptos_coin_AptosCoin'(false));

    // return ($t24, $t26) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:22:9+48
    $ret0 := $t24;
    $ret1 := $t26;
    return;

    // label L2 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:56:5+1
    assume {:print "$at(2,2057,2058)"} true;
L2:

    // trace_exp[subauto, at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:11:19+4]($t6) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:11:19+4
    assume {:print "$at(3,308,312)"} true;
    assume {:print "$track_exp_sub(28654):", $t6} true;

    // assume Identical($t53, Neq<address>($t6, 0x1)) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:11:9+35
    assume ($t53 == !$IsEqual'address'($t6, 1));

    // trace_exp[auto, at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:11:9+35]($t53) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:11:9+35
    assume {:print "$track_exp(28655):", $t53} true;

    // assume Identical($t54, string::spec_internal_check_utf8[]([65, 112, 116, 111, 115, 32, 67, 111, 105, 110])) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:12:20+47
    assume {:print "$at(3,353,400)"} true;
    assume ($t54 == $1_string_spec_internal_check_utf8(ConcatVec(ConcatVec(MakeVec4(65, 112, 116, 111), MakeVec4(115, 32, 67, 111)), MakeVec2(105, 110))));

    // trace_exp[subauto, at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:12:20+47]($t54) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:12:20+47
    assume {:print "$track_exp_sub(28658):", $t54} true;

    // assume Identical($t55, Not(string::spec_internal_check_utf8[]([65, 112, 116, 111, 115, 32, 67, 111, 105, 110]))) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:12:9+59
    assume ($t55 == !$1_string_spec_internal_check_utf8(ConcatVec(ConcatVec(MakeVec4(65, 112, 116, 111), MakeVec4(115, 32, 67, 111)), MakeVec2(105, 110))));

    // trace_exp[auto, at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:12:9+59]($t55) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:12:9+59
    assume {:print "$track_exp(28659):", $t55} true;

    // assume Identical($t56, string::spec_internal_check_utf8[]([65, 80, 84])) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:13:20+40
    assume {:print "$at(3,421,461)"} true;
    assume ($t56 == $1_string_spec_internal_check_utf8(MakeVec3(65, 80, 84)));

    // trace_exp[subauto, at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:13:20+40]($t56) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:13:20+40
    assume {:print "$track_exp_sub(28662):", $t56} true;

    // assume Identical($t57, Not(string::spec_internal_check_utf8[]([65, 80, 84]))) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:13:9+52
    assume ($t57 == !$1_string_spec_internal_check_utf8(MakeVec3(65, 80, 84)));

    // trace_exp[auto, at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:13:9+52]($t57) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:13:9+52
    assume {:print "$track_exp(28663):", $t57} true;

    // trace_exp[subauto, at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.spec.move:294:19+12]($t12) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.spec.move:294:19+12
    assume {:print "$at(94,12417,12429)"} true;
    assume {:print "$track_exp_sub(28668):", $t12} true;

    // trace_exp[subauto, at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.spec.move:294:35+12]($t9) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.spec.move:294:35+12
    assume {:print "$track_exp_sub(28670):", $t9} true;

    // assume Identical($t58, Neq<address>($t12, $t9)) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.spec.move:294:9+39
    assume ($t58 == !$IsEqual'address'($t12, $t9));

    // trace_exp[auto, at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.spec.move:294:9+39]($t58) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.spec.move:294:9+39
    assume {:print "$track_exp(28671):", $t58} true;

    // trace_exp[subauto, at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.spec.move:295:46+12]($t9) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.spec.move:295:46+12
    assume {:print "$at(94,12492,12504)"} true;
    assume {:print "$track_exp_sub(28676):", $t9} true;

    // assume Identical($t59, exists[@27]<coin::CoinInfo<aptos_coin::AptosCoin>>($t9)) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.spec.move:295:19+40
    assume ($t59 == $ResourceExists($1_coin_CoinInfo'$1_aptos_coin_AptosCoin'_$memory#27, $t9));

    // trace_exp[subauto, at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.spec.move:295:19+40]($t59) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.spec.move:295:19+40
    assume {:print "$track_exp_sub(28677):", $t59} true;

    // assume Identical($t60, exists[@27]<coin::CoinInfo<aptos_coin::AptosCoin>>($t9)) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.spec.move:295:9+51
    assume ($t60 == $ResourceExists($1_coin_CoinInfo'$1_aptos_coin_AptosCoin'_$memory#27, $t9));

    // trace_exp[auto, at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.spec.move:295:9+51]($t60) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.spec.move:295:9+51
    assume {:print "$track_exp(28678):", $t60} true;

    // assume Identical($t61, Gt(Len<u8>([65, 112, 116, 111, 115, 32, 67, 111, 105, 110]), 32)) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.spec.move:296:9+43
    assume {:print "$at(94,12515,12558)"} true;
    assume ($t61 == (LenVec(ConcatVec(ConcatVec(MakeVec4(65, 112, 116, 111), MakeVec4(115, 32, 67, 111)), MakeVec2(105, 110))) > 32));

    // trace_exp[auto, at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.spec.move:296:9+43]($t61) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.spec.move:296:9+43
    assume {:print "$track_exp(28680):", $t61} true;

    // assume Identical($t62, Gt(Len<u8>([65, 80, 84]), 10)) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.spec.move:297:9+47
    assume {:print "$at(94,12567,12614)"} true;
    assume ($t62 == (LenVec(MakeVec3(65, 80, 84)) > 10));

    // trace_exp[auto, at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.spec.move:297:9+47]($t62) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.spec.move:297:9+47
    assume {:print "$track_exp(28682):", $t62} true;

    // assume Identical($t63, exists[@28]<aggregator_factory::AggregatorFactory>(0x1)) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:15:20+80
    assume {:print "$at(3,607,687)"} true;
    assume ($t63 == $ResourceExists($1_aggregator_factory_AggregatorFactory_$memory#28, 1));

    // trace_exp[subauto, at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:15:20+80]($t63) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:15:20+80
    assume {:print "$track_exp_sub(28685):", $t63} true;

    // assume Identical($t64, Not(exists[@28]<aggregator_factory::AggregatorFactory>(0x1))) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:15:9+92
    assume ($t64 == !$ResourceExists($1_aggregator_factory_AggregatorFactory_$memory#28, 1));

    // trace_exp[auto, at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:15:9+92]($t64) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:15:9+92
    assume {:print "$track_exp(28686):", $t64} true;

    // trace_exp[subauto, at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:16:40+4]($t6) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:16:40+4
    assume {:print "$at(3,728,732)"} true;
    assume {:print "$track_exp_sub(28691):", $t6} true;

    // assume Identical($t65, exists[@29]<aptos_coin::MintCapStore>($t6)) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:16:19+26
    assume ($t65 == $ResourceExists($1_aptos_coin_MintCapStore_$memory#29, $t6));

    // trace_exp[subauto, at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:16:19+26]($t65) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:16:19+26
    assume {:print "$track_exp_sub(28692):", $t65} true;

    // assume Identical($t66, exists[@29]<aptos_coin::MintCapStore>($t6)) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:16:9+37
    assume ($t66 == $ResourceExists($1_aptos_coin_MintCapStore_$memory#29, $t6));

    // trace_exp[auto, at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:16:9+37]($t66) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:16:9+37
    assume {:print "$track_exp(28693):", $t66} true;

    // trace_global_mem() at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:16:9+37
    assume {:print "$track_global_mem(29222):", $1_aggregator_factory_AggregatorFactory_$memory} true;

    // trace_global_mem() at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:16:9+37
    assume {:print "$track_global_mem(29223):", $1_coin_CoinInfo'$1_aptos_coin_AptosCoin'_$memory} true;

    // trace_global_mem() at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:16:9+37
    assume {:print "$track_global_mem(29224):", $1_coin_Ghost$supply'$1_aptos_coin_AptosCoin'_$memory} true;

    // trace_global_mem() at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:16:9+37
    assume {:print "$track_global_mem(29225):", $1_coin_Ghost$aggregate_supply'$1_aptos_coin_AptosCoin'_$memory} true;

    // trace_global_mem() at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:16:9+37
    assume {:print "$track_global_mem(29226):", $1_aptos_coin_MintCapStore_$memory} true;

    // assert Or(Or(Or(Or(Or(Or(Or(Or(Neq<address>($t6, 0x1), Not(string::spec_internal_check_utf8[]([65, 112, 116, 111, 115, 32, 67, 111, 105, 110]))), Not(string::spec_internal_check_utf8[]([65, 80, 84]))), Neq<address>($t12, $t9)), exists[@27]<coin::CoinInfo<aptos_coin::AptosCoin>>($t9)), Gt(Len<u8>([65, 112, 116, 111, 115, 32, 67, 111, 105, 110]), 32)), Gt(Len<u8>([65, 80, 84]), 10)), Not(exists[@28]<aggregator_factory::AggregatorFactory>(0x1))), exists[@29]<aptos_coin::MintCapStore>($t6)) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:7:5+943
    assume {:print "$at(3,130,1073)"} true;
    assert {:msg "assert_failed(3,130,1073): abort not covered by any of the `aborts_if` clauses"}
      ((((((((!$IsEqual'address'($t6, 1) || !$1_string_spec_internal_check_utf8(ConcatVec(ConcatVec(MakeVec4(65, 112, 116, 111), MakeVec4(115, 32, 67, 111)), MakeVec2(105, 110)))) || !$1_string_spec_internal_check_utf8(MakeVec3(65, 80, 84))) || !$IsEqual'address'($t12, $t9)) || $ResourceExists($1_coin_CoinInfo'$1_aptos_coin_AptosCoin'_$memory#27, $t9)) || (LenVec(ConcatVec(ConcatVec(MakeVec4(65, 112, 116, 111), MakeVec4(115, 32, 67, 111)), MakeVec2(105, 110))) > 32)) || (LenVec(MakeVec3(65, 80, 84)) > 10)) || !$ResourceExists($1_aggregator_factory_AggregatorFactory_$memory#28, 1)) || $ResourceExists($1_aptos_coin_MintCapStore_$memory#29, $t6));

    // abort($t14) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:7:5+943
    $abort_code := $t14;
    $abort_flag := true;
    return;

}

// fun aptos_coin::destroy_mint_cap [verification] at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:64:5+283
procedure {:timeLimit 40} $1_aptos_coin_destroy_mint_cap$verify(_$t0: $signer) returns ()
{
    // declare local variables
    var $t1: int;
    var $t2: int;
    var $t3: int;
    var $t4: bool;
    var $t5: int;
    var $t6: int;
    var $t7: $1_aptos_coin_MintCapStore;
    var $t8: $1_coin_MintCapability'$1_aptos_coin_AptosCoin';
    var $t9: $1_option_Option'$1_optional_aggregator_OptionalAggregator';
    var $t10: bool;
    var $t11: bool;
    var $t12: bool;
    var $t13: bool;
    var $t14: bool;
    var $t15: bool;
    var $t16: bool;
    var $t17: bool;
    var $t0: $signer;
    var $temp_0'address': int;
    var $temp_0'bool': bool;
    var $temp_0'signer': $signer;
    var $1_aptos_coin_MintCapStore_$memory#23: $Memory $1_aptos_coin_MintCapStore;
    $t0 := _$t0;

    // verification entrypoint assumptions
    call $InitVerification();

    // bytecode translation starts here
    // assume WellFormed($t0) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:64:5+1
    assume {:print "$at(2,2369,2370)"} true;
    assume $IsValid'signer'($t0) && $1_signer_is_txn_signer($t0) && $1_signer_is_txn_signer_addr($addr#$signer($t0));

    // assume forall $rsc: ResourceDomain<coin::CoinInfo<aptos_coin::AptosCoin>>(): And(WellFormed($rsc), And(Le(Len<optional_aggregator::OptionalAggregator>(select option::Option.vec(select coin::CoinInfo.supply($rsc))), 1), forall $elem: select option::Option.vec(select coin::CoinInfo.supply($rsc)): And(And(And(And(And(Iff(option::$is_some<aggregator::Aggregator>(select optional_aggregator::OptionalAggregator.aggregator($elem)), option::$is_none<optional_aggregator::Integer>(select optional_aggregator::OptionalAggregator.integer($elem))), Iff(option::$is_some<optional_aggregator::Integer>(select optional_aggregator::OptionalAggregator.integer($elem)), option::$is_none<aggregator::Aggregator>(select optional_aggregator::OptionalAggregator.aggregator($elem)))), Implies(option::$is_some<optional_aggregator::Integer>(select optional_aggregator::OptionalAggregator.integer($elem)), Le(select optional_aggregator::Integer.value(option::$borrow<optional_aggregator::Integer>(select optional_aggregator::OptionalAggregator.integer($elem))), select optional_aggregator::Integer.limit(option::$borrow<optional_aggregator::Integer>(select optional_aggregator::OptionalAggregator.integer($elem)))))), Implies(option::$is_some<aggregator::Aggregator>(select optional_aggregator::OptionalAggregator.aggregator($elem)), Le(aggregator::spec_aggregator_get_val(option::$borrow<aggregator::Aggregator>(select optional_aggregator::OptionalAggregator.aggregator($elem))), aggregator::spec_get_limit(option::$borrow<aggregator::Aggregator>(select optional_aggregator::OptionalAggregator.aggregator($elem)))))), Le(Len<aggregator::Aggregator>(select option::Option.vec(select optional_aggregator::OptionalAggregator.aggregator($elem))), 1)), Le(Len<optional_aggregator::Integer>(select option::Option.vec(select optional_aggregator::OptionalAggregator.integer($elem))), 1)))) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:64:5+1
    assume (forall $a_0: int :: {$ResourceValue($1_coin_CoinInfo'$1_aptos_coin_AptosCoin'_$memory, $a_0)}(var $rsc := $ResourceValue($1_coin_CoinInfo'$1_aptos_coin_AptosCoin'_$memory, $a_0);
    (($IsValid'$1_coin_CoinInfo'$1_aptos_coin_AptosCoin''($rsc) && ((LenVec($vec#$1_option_Option'$1_optional_aggregator_OptionalAggregator'($supply#$1_coin_CoinInfo'$1_aptos_coin_AptosCoin'($rsc))) <= 1) && (var $range_1 := $vec#$1_option_Option'$1_optional_aggregator_OptionalAggregator'($supply#$1_coin_CoinInfo'$1_aptos_coin_AptosCoin'($rsc)); (forall $i_2: int :: InRangeVec($range_1, $i_2) ==> (var $elem := ReadVec($range_1, $i_2);
    ((((((($1_option_$is_some'$1_aggregator_Aggregator'($aggregator#$1_optional_aggregator_OptionalAggregator($elem)) <==> $1_option_$is_none'$1_optional_aggregator_Integer'($integer#$1_optional_aggregator_OptionalAggregator($elem))) && ($1_option_$is_some'$1_optional_aggregator_Integer'($integer#$1_optional_aggregator_OptionalAggregator($elem)) <==> $1_option_$is_none'$1_aggregator_Aggregator'($aggregator#$1_optional_aggregator_OptionalAggregator($elem)))) && ($1_option_$is_some'$1_optional_aggregator_Integer'($integer#$1_optional_aggregator_OptionalAggregator($elem)) ==> ($value#$1_optional_aggregator_Integer($1_option_$borrow'$1_optional_aggregator_Integer'($integer#$1_optional_aggregator_OptionalAggregator($elem))) <= $limit#$1_optional_aggregator_Integer($1_option_$borrow'$1_optional_aggregator_Integer'($integer#$1_optional_aggregator_OptionalAggregator($elem)))))) && ($1_option_$is_some'$1_aggregator_Aggregator'($aggregator#$1_optional_aggregator_OptionalAggregator($elem)) ==> ($1_aggregator_spec_aggregator_get_val($1_option_$borrow'$1_aggregator_Aggregator'($aggregator#$1_optional_aggregator_OptionalAggregator($elem))) <= $1_aggregator_spec_get_limit($1_option_$borrow'$1_aggregator_Aggregator'($aggregator#$1_optional_aggregator_OptionalAggregator($elem)))))) && (LenVec($vec#$1_option_Option'$1_aggregator_Aggregator'($aggregator#$1_optional_aggregator_OptionalAggregator($elem))) <= 1)) && (LenVec($vec#$1_option_Option'$1_optional_aggregator_Integer'($integer#$1_optional_aggregator_OptionalAggregator($elem))) <= 1)))))))))));

    // assume forall $rsc: ResourceDomain<coin::Ghost$supply<aptos_coin::AptosCoin>>(): WellFormed($rsc) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:64:5+1
    assume (forall $a_0: int :: {$ResourceValue($1_coin_Ghost$supply'$1_aptos_coin_AptosCoin'_$memory, $a_0)}(var $rsc := $ResourceValue($1_coin_Ghost$supply'$1_aptos_coin_AptosCoin'_$memory, $a_0);
    ($IsValid'$1_coin_Ghost$supply'$1_aptos_coin_AptosCoin''($rsc))));

    // assume exists<coin::Ghost$supply<aptos_coin::AptosCoin>>(0x0) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:64:5+1
    assume $ResourceExists($1_coin_Ghost$supply'$1_aptos_coin_AptosCoin'_$memory, 0);

    // assume forall $rsc: ResourceDomain<coin::Ghost$aggregate_supply<aptos_coin::AptosCoin>>(): WellFormed($rsc) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:64:5+1
    assume (forall $a_0: int :: {$ResourceValue($1_coin_Ghost$aggregate_supply'$1_aptos_coin_AptosCoin'_$memory, $a_0)}(var $rsc := $ResourceValue($1_coin_Ghost$aggregate_supply'$1_aptos_coin_AptosCoin'_$memory, $a_0);
    ($IsValid'$1_coin_Ghost$aggregate_supply'$1_aptos_coin_AptosCoin''($rsc))));

    // assume exists<coin::Ghost$aggregate_supply<aptos_coin::AptosCoin>>(0x0) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:64:5+1
    assume $ResourceExists($1_coin_Ghost$aggregate_supply'$1_aptos_coin_AptosCoin'_$memory, 0);

    // assume forall $rsc: ResourceDomain<aptos_coin::MintCapStore>(): WellFormed($rsc) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:64:5+1
    assume (forall $a_0: int :: {$ResourceValue($1_aptos_coin_MintCapStore_$memory, $a_0)}(var $rsc := $ResourceValue($1_aptos_coin_MintCapStore_$memory, $a_0);
    ($IsValid'$1_aptos_coin_MintCapStore'($rsc))));

    // trace_exp[subauto, at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:26:39+15]($t0) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:26:39+15
    assume {:print "$at(3,1141,1156)"} true;
    assume {:print "$track_exp_sub(28471):", $t0} true;

    // assume Identical($t1, signer::$address_of($t0)) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:26:20+35
    assume ($t1 == $1_signer_$address_of($t0));

    // trace_exp[subauto, at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:26:20+35]($t1) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:26:20+35
    assume {:print "$track_exp_sub(28472):", $t1} true;

    // assume Identical($t2, signer::$address_of($t0)) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:26:9+47
    assume ($t2 == $1_signer_$address_of($t0));

    // trace_exp[auto, at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:26:9+47]($t2) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:26:9+47
    assume {:print "$track_exp(28473):", $t2} true;

    // trace_global_mem() at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:26:9+47
    assume {:print "$track_global_mem(29227):", $1_coin_CoinInfo'$1_aptos_coin_AptosCoin'_$memory} true;

    // trace_global_mem() at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:26:9+47
    assume {:print "$track_global_mem(29228):", $1_coin_Ghost$supply'$1_aptos_coin_AptosCoin'_$memory} true;

    // trace_global_mem() at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:26:9+47
    assume {:print "$track_global_mem(29229):", $1_coin_Ghost$aggregate_supply'$1_aptos_coin_AptosCoin'_$memory} true;

    // trace_global_mem() at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:26:9+47
    assume {:print "$track_global_mem(29230):", $1_aptos_coin_MintCapStore_$memory} true;

    // assume Identical($t3, signer::$address_of($t0)) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:26:9+47
    assume ($t3 == $1_signer_$address_of($t0));

    // @23 := save_mem(aptos_coin::MintCapStore) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:64:5+1
    assume {:print "$at(2,2369,2370)"} true;
    $1_aptos_coin_MintCapStore_$memory#23 := $1_aptos_coin_MintCapStore_$memory;

    // trace_local[aptos_framework]($t0) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:64:5+1
    assume {:print "$track_local(24,3,0):", $t0} $t0 == $t0;

    // opaque begin: system_addresses::assert_aptos_framework($t0) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:65:9+57
    assume {:print "$at(2,2463,2520)"} true;

    // assume Identical($t4, Neq<address>(signer::$address_of($t0), 0x1)) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:65:9+57
    assume ($t4 == !$IsEqual'address'($1_signer_$address_of($t0), 1));

    // if ($t4) goto L4 else goto L3 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:65:9+57
    if ($t4) { goto L4; } else { goto L3; }

    // label L4 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:65:9+57
L4:

    // trace_global_mem() at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:65:9+57
    assume {:print "$at(2,2463,2520)"} true;
    assume {:print "$track_global_mem(29231):", $1_coin_CoinInfo'$1_aptos_coin_AptosCoin'_$memory} true;

    // trace_global_mem() at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:65:9+57
    assume {:print "$track_global_mem(29232):", $1_coin_Ghost$supply'$1_aptos_coin_AptosCoin'_$memory} true;

    // trace_global_mem() at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:65:9+57
    assume {:print "$track_global_mem(29233):", $1_coin_Ghost$aggregate_supply'$1_aptos_coin_AptosCoin'_$memory} true;

    // trace_global_mem() at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:65:9+57
    assume {:print "$track_global_mem(29234):", $1_aptos_coin_MintCapStore_$memory} true;

    // assume And(Neq<address>(signer::$address_of($t0), 0x1), Eq(5, $t5)) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:65:9+57
    assume (!$IsEqual'address'($1_signer_$address_of($t0), 1) && $IsEqual'num'(5, $t5));

    // trace_abort($t5) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:65:9+57
    assume {:print "$at(2,2463,2520)"} true;
    assume {:print "$track_abort(24,3):", $t5} $t5 == $t5;

    // goto L2 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:65:9+57
    goto L2;

    // label L3 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:65:9+57
L3:

    // opaque end: system_addresses::assert_aptos_framework($t0) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:65:9+57
    assume {:print "$at(2,2463,2520)"} true;

    // $t6 := 0x1 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:66:65+16
    assume {:print "$at(2,2586,2602)"} true;
    $t6 := 1;
    assume $IsValid'address'($t6);

    // $t7 := move_from<aptos_coin::MintCapStore>($t6) on_abort goto L2 with $t5 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:66:41+9
    if (!$ResourceExists($1_aptos_coin_MintCapStore_$memory, $t6)) {
        call $ExecFailureAbort();
    } else {
        $t7 := $ResourceValue($1_aptos_coin_MintCapStore_$memory, $t6);
        $1_aptos_coin_MintCapStore_$memory := $ResourceRemove($1_aptos_coin_MintCapStore_$memory, $t6);
    }
    if ($abort_flag) {
        assume {:print "$at(2,2562,2571)"} true;
        $t5 := $abort_code;
        assume {:print "$track_abort(24,3):", $t5} $t5 == $t5;
        goto L2;
    }

    // $t8 := unpack aptos_coin::MintCapStore($t7) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:66:13+25
    $t8 := $mint_cap#$1_aptos_coin_MintCapStore($t7);

    // trace_global_mem() at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:67:9+32
    assume {:print "$at(2,2613,2645)"} true;
    assume {:print "$track_global_mem(29235):", $1_coin_CoinInfo'$1_aptos_coin_AptosCoin'_$memory} true;

    // trace_global_mem() at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:67:9+32
    assume {:print "$track_global_mem(29236):", $1_coin_Ghost$supply'$1_aptos_coin_AptosCoin'_$memory} true;

    // trace_global_mem() at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:67:9+32
    assume {:print "$track_global_mem(29237):", $1_coin_Ghost$aggregate_supply'$1_aptos_coin_AptosCoin'_$memory} true;

    // trace_global_mem() at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:67:9+32
    assume {:print "$track_global_mem(29238):", $1_aptos_coin_MintCapStore_$memory} true;

    // assume Identical($t9, select coin::CoinInfo.supply(global<coin::CoinInfo<aptos_coin::AptosCoin>>(select type_info::TypeInfo.account_address(type_info::$type_of<aptos_coin::AptosCoin>())))) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/coin.spec.move:32:9+99
    assume {:print "$at(94,1664,1763)"} true;
    assume ($t9 == $supply#$1_coin_CoinInfo'$1_aptos_coin_AptosCoin'($ResourceValue($1_coin_CoinInfo'$1_aptos_coin_AptosCoin'_$memory, $account_address#$1_type_info_TypeInfo($1_type_info_TypeInfo(1, Vec(DefaultVecMap()[0 := 97][1 := 112][2 := 116][3 := 111][4 := 115][5 := 95][6 := 99][7 := 111][8 := 105][9 := 110], 10), Vec(DefaultVecMap()[0 := 65][1 := 112][2 := 116][3 := 111][4 := 115][5 := 67][6 := 111][7 := 105][8 := 110], 9))))));

    // coin::destroy_mint_cap<aptos_coin::AptosCoin>($t8) on_abort goto L2 with $t5 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:67:9+32
    assume {:print "$at(2,2613,2645)"} true;
    call $1_coin_destroy_mint_cap'$1_aptos_coin_AptosCoin'($t8);
    if ($abort_flag) {
        assume {:print "$at(2,2613,2645)"} true;
        $t5 := $abort_code;
        assume {:print "$track_abort(24,3):", $t5} $t5 == $t5;
        goto L2;
    }

    // label L1 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:68:5+1
    assume {:print "$at(2,2651,2652)"} true;
L1:

    // trace_exp[subauto, at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:27:19+4]($t3) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:27:19+4
    assume {:print "$at(3,1177,1181)"} true;
    assume {:print "$track_exp_sub(28477):", $t3} true;

    // assume Identical($t10, Neq<address>($t3, 0x1)) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:27:9+35
    assume ($t10 == !$IsEqual'address'($t3, 1));

    // trace_exp[auto, at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:27:9+35]($t10) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:27:9+35
    assume {:print "$track_exp(28478):", $t10} true;

    // trace_global_mem() at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:27:9+35
    assume {:print "$track_global_mem(29239):", $1_coin_CoinInfo'$1_aptos_coin_AptosCoin'_$memory} true;

    // trace_global_mem() at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:27:9+35
    assume {:print "$track_global_mem(29240):", $1_coin_Ghost$supply'$1_aptos_coin_AptosCoin'_$memory} true;

    // trace_global_mem() at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:27:9+35
    assume {:print "$track_global_mem(29241):", $1_coin_Ghost$aggregate_supply'$1_aptos_coin_AptosCoin'_$memory} true;

    // trace_global_mem() at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:27:9+35
    assume {:print "$track_global_mem(29242):", $1_aptos_coin_MintCapStore_$memory} true;

    // assert Not(Neq<address>($t3, 0x1)) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:27:9+35
    assert {:msg "assert_failed(3,1167,1202): function does not abort under this condition"}
      !!$IsEqual'address'($t3, 1);

    // assume Identical($t11, exists[@23]<aptos_coin::MintCapStore>(0x1)) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:28:20+38
    assume {:print "$at(3,1222,1260)"} true;
    assume ($t11 == $ResourceExists($1_aptos_coin_MintCapStore_$memory#23, 1));

    // trace_exp[subauto, at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:28:20+38]($t11) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:28:20+38
    assume {:print "$track_exp_sub(28481):", $t11} true;

    // assume Identical($t12, Not(exists[@23]<aptos_coin::MintCapStore>(0x1))) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:28:9+50
    assume ($t12 == !$ResourceExists($1_aptos_coin_MintCapStore_$memory#23, 1));

    // trace_exp[auto, at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:28:9+50]($t12) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:28:9+50
    assume {:print "$track_exp(28482):", $t12} true;

    // trace_global_mem() at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:28:9+50
    assume {:print "$track_global_mem(29243):", $1_coin_CoinInfo'$1_aptos_coin_AptosCoin'_$memory} true;

    // trace_global_mem() at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:28:9+50
    assume {:print "$track_global_mem(29244):", $1_coin_Ghost$supply'$1_aptos_coin_AptosCoin'_$memory} true;

    // trace_global_mem() at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:28:9+50
    assume {:print "$track_global_mem(29245):", $1_coin_Ghost$aggregate_supply'$1_aptos_coin_AptosCoin'_$memory} true;

    // trace_global_mem() at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:28:9+50
    assume {:print "$track_global_mem(29246):", $1_aptos_coin_MintCapStore_$memory} true;

    // assert Not(Not(exists[@23]<aptos_coin::MintCapStore>(0x1))) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:28:9+50
    assert {:msg "assert_failed(3,1211,1261): function does not abort under this condition"}
      !!$ResourceExists($1_aptos_coin_MintCapStore_$memory#23, 1);

    // assume Identical($t13, exists<aptos_coin::MintCapStore>(0x1)) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:30:18+38
    assume {:print "$at(3,1280,1318)"} true;
    assume ($t13 == $ResourceExists($1_aptos_coin_MintCapStore_$memory, 1));

    // trace_exp[subauto, at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:30:18+38]($t13) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:30:18+38
    assume {:print "$track_exp_sub(28485):", $t13} true;

    // assume Identical($t14, Not(exists<aptos_coin::MintCapStore>(0x1))) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:30:9+48
    assume ($t14 == !$ResourceExists($1_aptos_coin_MintCapStore_$memory, 1));

    // trace_exp[auto, at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:30:9+48]($t14) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:30:9+48
    assume {:print "$track_exp(28486):", $t14} true;

    // trace_global_mem() at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:30:9+48
    assume {:print "$track_global_mem(29247):", $1_coin_CoinInfo'$1_aptos_coin_AptosCoin'_$memory} true;

    // trace_global_mem() at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:30:9+48
    assume {:print "$track_global_mem(29248):", $1_coin_Ghost$supply'$1_aptos_coin_AptosCoin'_$memory} true;

    // trace_global_mem() at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:30:9+48
    assume {:print "$track_global_mem(29249):", $1_coin_Ghost$aggregate_supply'$1_aptos_coin_AptosCoin'_$memory} true;

    // trace_global_mem() at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:30:9+48
    assume {:print "$track_global_mem(29250):", $1_aptos_coin_MintCapStore_$memory} true;

    // assert Not(exists<aptos_coin::MintCapStore>(0x1)) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:30:9+48
    assert {:msg "assert_failed(3,1271,1319): post-condition does not hold"}
      !$ResourceExists($1_aptos_coin_MintCapStore_$memory, 1);

    // return () at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:30:9+48
    return;

    // label L2 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:68:5+1
    assume {:print "$at(2,2651,2652)"} true;
L2:

    // trace_exp[subauto, at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:27:19+4]($t3) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:27:19+4
    assume {:print "$at(3,1177,1181)"} true;
    assume {:print "$track_exp_sub(28477):", $t3} true;

    // assume Identical($t15, Neq<address>($t3, 0x1)) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:27:9+35
    assume ($t15 == !$IsEqual'address'($t3, 1));

    // trace_exp[auto, at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:27:9+35]($t15) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:27:9+35
    assume {:print "$track_exp(28478):", $t15} true;

    // assume Identical($t16, exists[@23]<aptos_coin::MintCapStore>(0x1)) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:28:20+38
    assume {:print "$at(3,1222,1260)"} true;
    assume ($t16 == $ResourceExists($1_aptos_coin_MintCapStore_$memory#23, 1));

    // trace_exp[subauto, at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:28:20+38]($t16) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:28:20+38
    assume {:print "$track_exp_sub(28481):", $t16} true;

    // assume Identical($t17, Not(exists[@23]<aptos_coin::MintCapStore>(0x1))) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:28:9+50
    assume ($t17 == !$ResourceExists($1_aptos_coin_MintCapStore_$memory#23, 1));

    // trace_exp[auto, at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:28:9+50]($t17) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:28:9+50
    assume {:print "$track_exp(28482):", $t17} true;

    // trace_global_mem() at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:28:9+50
    assume {:print "$track_global_mem(29251):", $1_coin_CoinInfo'$1_aptos_coin_AptosCoin'_$memory} true;

    // trace_global_mem() at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:28:9+50
    assume {:print "$track_global_mem(29252):", $1_coin_Ghost$supply'$1_aptos_coin_AptosCoin'_$memory} true;

    // trace_global_mem() at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:28:9+50
    assume {:print "$track_global_mem(29253):", $1_coin_Ghost$aggregate_supply'$1_aptos_coin_AptosCoin'_$memory} true;

    // trace_global_mem() at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:28:9+50
    assume {:print "$track_global_mem(29254):", $1_aptos_coin_MintCapStore_$memory} true;

    // assert Or(Neq<address>($t3, 0x1), Not(exists[@23]<aptos_coin::MintCapStore>(0x1))) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:25:5+246
    assume {:print "$at(3,1079,1325)"} true;
    assert {:msg "assert_failed(3,1079,1325): abort not covered by any of the `aborts_if` clauses"}
      (!$IsEqual'address'($t3, 1) || !$ResourceExists($1_aptos_coin_MintCapStore_$memory#23, 1));

    // abort($t5) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:25:5+246
    $abort_code := $t5;
    $abort_flag := true;
    return;

}

// fun aptos_coin::find_delegation [verification] at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:136:5+736
procedure {:timeLimit 40} $1_aptos_coin_find_delegation$verify(_$t0: int) returns ($ret0: $1_option_Option'u64')
{
    // declare local variables
    var $t1: Vec ($1_aptos_coin_DelegatedMintCapability);
    var $t2: int;
    var $t3: $1_option_Option'u64';
    var $t4: int;
    var $t5: $1_aptos_coin_Delegations;
    var $t6: Vec ($1_aptos_coin_DelegatedMintCapability);
    var $t7: Vec ($1_aptos_coin_DelegatedMintCapability);
    var $t8: int;
    var $t9: $1_aptos_coin_Delegations;
    var $t10: int;
    var $t11: Vec ($1_aptos_coin_DelegatedMintCapability);
    var $t12: int;
    var $t13: int;
    var $t14: $1_option_Option'u64';
    var $t15: bool;
    var $t16: bool;
    var $t17: bool;
    var $t18: bool;
    var $t19: bool;
    var $t20: bool;
    var $t21: bool;
    var $t22: $1_aptos_coin_DelegatedMintCapability;
    var $t23: bool;
    var $t24: int;
    var $t25: bool;
    var $t26: bool;
    var $t27: bool;
    var $t28: int;
    var $t29: bool;
    var $t30: int;
    var $t31: bool;
    var $t32: bool;
    var $t33: bool;
    var $t34: bool;
    var $t35: bool;
    var $t36: bool;
    var $t37: $1_option_Option'u64';
    var $t38: int;
    var $t39: bool;
    var $t40: bool;
    var $t41: bool;
    var $t42: bool;
    var $t43: bool;
    var $t44: bool;
    var $t45: int;
    var $t46: int;
    var $t47: bool;
    var $t48: bool;
    var $t49: bool;
    var $t50: bool;
    var $t51: bool;
    var $t0: int;
    var $temp_0'$1_aptos_coin_DelegatedMintCapability': $1_aptos_coin_DelegatedMintCapability;
    var $temp_0'$1_aptos_coin_Delegations': $1_aptos_coin_Delegations;
    var $temp_0'$1_option_Option'u64'': $1_option_Option'u64';
    var $temp_0'address': int;
    var $temp_0'bool': bool;
    var $temp_0'u64': int;
    var $temp_0'vec'$1_aptos_coin_DelegatedMintCapability'': Vec ($1_aptos_coin_DelegatedMintCapability);
    var $1_aptos_coin_Delegations_$memory#21: $Memory $1_aptos_coin_Delegations;
    $t0 := _$t0;

    // verification entrypoint assumptions
    call $InitVerification();

    // bytecode translation starts here
    // assume WellFormed($t0) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:136:5+1
    assume {:print "$at(2,5735,5736)"} true;
    assume $IsValid'address'($t0);

    // assume forall $rsc: ResourceDomain<aptos_coin::Delegations>(): WellFormed($rsc) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:136:5+1
    assume (forall $a_0: int :: {$ResourceValue($1_aptos_coin_Delegations_$memory, $a_0)}(var $rsc := $ResourceValue($1_aptos_coin_Delegations_$memory, $a_0);
    ($IsValid'$1_aptos_coin_Delegations'($rsc))));

    // assume Identical($t5, global<aptos_coin::Delegations>(0xa550c18)) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:56:27+36
    assume {:print "$at(3,1986,2022)"} true;
    assume ($t5 == $ResourceValue($1_aptos_coin_Delegations_$memory, 173345816));

    // trace_exp[subauto, at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:56:27+36]($t5) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:56:27+36
    assume {:print "$track_exp_sub(28205):", $t5} true;

    // assume Identical($t6, select aptos_coin::Delegations.inner(global<aptos_coin::Delegations>(0xa550c18))) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:56:9+61
    assume ($t6 == $inner#$1_aptos_coin_Delegations($ResourceValue($1_aptos_coin_Delegations_$memory, 173345816)));

    // trace_exp[auto, at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:56:9+61]($t6) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:56:9+61
    assume {:print "$track_exp(28206):", $t6} true;

    // trace_global_mem() at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:56:9+61
    assume {:print "$track_global_mem(29255):", $1_aptos_coin_Delegations_$memory} true;

    // assume Identical($t7, select aptos_coin::Delegations.inner(global<aptos_coin::Delegations>(0xa550c18))) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:56:9+61
    assume ($t7 == $inner#$1_aptos_coin_Delegations($ResourceValue($1_aptos_coin_Delegations_$memory, 173345816)));

    // @21 := save_mem(aptos_coin::Delegations) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:136:5+1
    assume {:print "$at(2,5735,5736)"} true;
    $1_aptos_coin_Delegations_$memory#21 := $1_aptos_coin_Delegations_$memory;

    // trace_local[addr]($t0) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:136:5+1
    assume {:print "$track_local(24,4,0):", $t0} $t0 == $t0;

    // $t8 := 0xa550c18 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:137:55+15
    assume {:print "$at(2,5860,5875)"} true;
    $t8 := 173345816;
    assume $IsValid'address'($t8);

    // $t9 := get_global<aptos_coin::Delegations>($t8) on_abort goto L8 with $t10 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:137:28+13
    if (!$ResourceExists($1_aptos_coin_Delegations_$memory, $t8)) {
        call $ExecFailureAbort();
    } else {
        $t9 := $ResourceValue($1_aptos_coin_Delegations_$memory, $t8);
    }
    if ($abort_flag) {
        assume {:print "$at(2,5833,5846)"} true;
        $t10 := $abort_code;
        assume {:print "$track_abort(24,4):", $t10} $t10 == $t10;
        goto L8;
    }

    // $t11 := get_field<aptos_coin::Delegations>.inner($t9) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:137:27+50
    $t11 := $inner#$1_aptos_coin_Delegations($t9);

    // trace_local[delegations]($t11) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:137:13+11
    assume {:print "$track_local(24,4,1):", $t11} $t11 == $t11;

    // $t12 := 0 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:138:17+1
    assume {:print "$at(2,5900,5901)"} true;
    $t12 := 0;
    assume $IsValid'u64'($t12);

    // trace_local[i]($t12) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:138:13+1
    assume {:print "$track_local(24,4,2):", $t12} $t12 == $t12;

    // $t13 := vector::length<aptos_coin::DelegatedMintCapability>($t11) on_abort goto L8 with $t10 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:139:19+27
    assume {:print "$at(2,5921,5948)"} true;
    call $t13 := $1_vector_length'$1_aptos_coin_DelegatedMintCapability'($t11);
    if ($abort_flag) {
        assume {:print "$at(2,5921,5948)"} true;
        $t10 := $abort_code;
        assume {:print "$track_abort(24,4):", $t10} $t10 == $t10;
        goto L8;
    }

    // trace_local[len]($t13) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:139:13+3
    assume {:print "$track_local(24,4,4):", $t13} $t13 == $t13;

    // $t14 := opaque begin: option::none<u64>() at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:140:21+14
    assume {:print "$at(2,5970,5984)"} true;

    // assume And(WellFormed($t14), Le(Len<u64>(select option::Option.vec($t14)), 1)) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:140:21+14
    assume ($IsValid'$1_option_Option'u64''($t14) && (LenVec($vec#$1_option_Option'u64'($t14)) <= 1));

    // trace_global_mem() at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:140:21+14
    assume {:print "$track_global_mem(29256):", $1_aptos_coin_Delegations_$memory} true;

    // assume Eq<option::Option<u64>>($t14, option::spec_none<u64>()) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:140:21+14
    assume $IsEqual'$1_option_Option'u64''($t14, $1_option_spec_none'u64'());

    // $t14 := opaque end: option::none<u64>() at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:140:21+14

    // $t3 := $t14 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:140:13+5
    $t3 := $t14;

    // trace_local[index]($t14) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:140:13+5
    assume {:print "$track_local(24,4,3):", $t14} $t14 == $t14;

    // label L5 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:142:13+192
    assume {:print "$at(2,6015,6207)"} true;
L5:

    // trace_exp[subauto, at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:143:27+1]($t12) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:143:27+1
    assume {:print "$at(2,6048,6049)"} true;
    assume {:print "$track_exp_sub(28255):", $t12} true;

    // trace_exp[subauto, at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:143:37+1]($t12) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:143:37+1
    assume {:print "$track_exp_sub(28256):", $t12} true;

    // trace_exp[subauto, at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:143:42+3]($t13) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:143:42+3
    assume {:print "$track_exp_sub(28257):", $t13} true;

    // assume Identical($t15, And(Ge($t12, 0), Le($t12, $t13))) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:143:17+29
    assume ($t15 == (($t12 >= 0) && ($t12 <= $t13)));

    // trace_exp[auto, at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:143:17+29]($t15) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:143:17+29
    assume {:print "$track_exp(28258):", $t15} true;

    // trace_global_mem() at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:143:17+29
    assume {:print "$track_global_mem(29257):", $1_aptos_coin_Delegations_$memory} true;

    // assert And(Ge($t12, 0), Le($t12, $t13)) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:143:17+29
    assert {:msg "assert_failed(2,6038,6067): base case of the loop invariant does not hold"}
      (($t12 >= 0) && ($t12 <= $t13));

    // trace_exp[subauto, at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:144:42+1]($t12) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:144:42+1
    assume {:print "$at(2,6109,6110)"} true;
    assume {:print "$track_exp_sub(28263):", $t12} true;

    // trace_exp[subauto, at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:144:45+11]($t11) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:144:45+11
    assume {:print "$track_exp_sub(28264):", $t11} true;

    // trace_exp[subauto, at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:144:66+4]($t0) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:144:66+4
    assume {:print "$track_exp_sub(28265):", $t0} true;

    // assume Identical($t16, forall j: Range(0, $t12): Neq<address>(select aptos_coin::DelegatedMintCapability.to(Index($t11, j)), $t0)) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:144:17+54
    assume ($t16 == (var $range_0 := $Range(0, $t12); (forall $i_1: int :: $InRange($range_0, $i_1) ==> (var j := $i_1;
    (!$IsEqual'address'($to#$1_aptos_coin_DelegatedMintCapability(ReadVec($t11, j)), $t0))))));

    // trace_exp[auto, at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:144:17+54]($t16) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:144:17+54
    assume {:print "$track_exp(28266):", $t16} true;

    // trace_global_mem() at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:144:17+54
    assume {:print "$track_global_mem(29258):", $1_aptos_coin_Delegations_$memory} true;

    // assert forall j: Range(0, $t12): Neq<address>(select aptos_coin::DelegatedMintCapability.to(Index($t11, j)), $t0) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:144:17+54
    assert {:msg "assert_failed(2,6084,6138): base case of the loop invariant does not hold"}
      (var $range_0 := $Range(0, $t12); (forall $i_1: int :: $InRange($range_0, $i_1) ==> (var j := $i_1;
    (!$IsEqual'address'($to#$1_aptos_coin_DelegatedMintCapability(ReadVec($t11, j)), $t0)))));

    // trace_exp[subauto, at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:145:48+5]($t14) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:145:48+5
    assume {:print "$at(2,6186,6191)"} true;
    assume {:print "$track_exp_sub(28270):", $t14} true;

    // assume Identical($t17, option::spec_is_none<u64>($t14)) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:145:27+27
    assume ($t17 == $1_option_spec_is_none'u64'($t14));

    // trace_exp[subauto, at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:145:27+27]($t17) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:145:27+27
    assume {:print "$track_exp_sub(28271):", $t17} true;

    // assume Identical($t18, option::spec_is_none<u64>($t14)) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:145:17+38
    assume ($t18 == $1_option_spec_is_none'u64'($t14));

    // trace_exp[auto, at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:145:17+38]($t18) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:145:17+38
    assume {:print "$track_exp(28272):", $t18} true;

    // trace_global_mem() at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:145:17+38
    assume {:print "$track_global_mem(29259):", $1_aptos_coin_Delegations_$memory} true;

    // assert option::spec_is_none<u64>($t14) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:145:17+38
    assert {:msg "assert_failed(2,6155,6193): base case of the loop invariant does not hold"}
      $1_option_spec_is_none'u64'($t14);

    // $t2 := havoc[val]() at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:145:17+38
    havoc $t2;

    // trace_exp[subauto, at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:145:17+38]($t2) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:145:17+38
    assume {:print "$track_exp_sub(28275):", $t2} true;

    // assume Identical($t19, WellFormed($t2)) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:145:17+38
    assume ($t19 == $IsValid'u64'($t2));

    // trace_exp[auto, at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:145:17+38]($t19) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:145:17+38
    assume {:print "$track_exp(28276):", $t19} true;

    // trace_global_mem() at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:145:17+38
    assume {:print "$track_global_mem(29260):", $1_aptos_coin_Delegations_$memory} true;

    // assume WellFormed($t2) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:145:17+38
    assume $IsValid'u64'($t2);

    // $t20 := havoc[val]() at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:145:17+38
    havoc $t20;

    // trace_exp[subauto, at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:145:17+38]($t20) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:145:17+38
    assume {:print "$track_exp_sub(28279):", $t20} true;

    // assume Identical($t21, WellFormed($t20)) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:145:17+38
    assume ($t21 == $IsValid'bool'($t20));

    // trace_exp[auto, at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:145:17+38]($t21) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:145:17+38
    assume {:print "$track_exp(28280):", $t21} true;

    // trace_global_mem() at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:145:17+38
    assume {:print "$track_global_mem(29261):", $1_aptos_coin_Delegations_$memory} true;

    // assume WellFormed($t20) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:145:17+38
    assume $IsValid'bool'($t20);

    // $t22 := havoc[val]() at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:145:17+38
    havoc $t22;

    // trace_exp[subauto, at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:145:17+38]($t22) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:145:17+38
    assume {:print "$track_exp_sub(28283):", $t22} true;

    // assume Identical($t23, WellFormed($t22)) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:145:17+38
    assume ($t23 == $IsValid'$1_aptos_coin_DelegatedMintCapability'($t22));

    // trace_exp[auto, at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:145:17+38]($t23) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:145:17+38
    assume {:print "$track_exp(28284):", $t23} true;

    // trace_global_mem() at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:145:17+38
    assume {:print "$track_global_mem(29262):", $1_aptos_coin_Delegations_$memory} true;

    // assume WellFormed($t22) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:145:17+38
    assume $IsValid'$1_aptos_coin_DelegatedMintCapability'($t22);

    // $t24 := havoc[val]() at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:145:17+38
    havoc $t24;

    // trace_exp[subauto, at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:145:17+38]($t24) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:145:17+38
    assume {:print "$track_exp_sub(28287):", $t24} true;

    // assume Identical($t25, WellFormed($t24)) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:145:17+38
    assume ($t25 == $IsValid'address'($t24));

    // trace_exp[auto, at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:145:17+38]($t25) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:145:17+38
    assume {:print "$track_exp(28288):", $t25} true;

    // trace_global_mem() at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:145:17+38
    assume {:print "$track_global_mem(29263):", $1_aptos_coin_Delegations_$memory} true;

    // assume WellFormed($t24) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:145:17+38
    assume $IsValid'address'($t24);

    // $t26 := havoc[val]() at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:145:17+38
    havoc $t26;

    // trace_exp[subauto, at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:145:17+38]($t26) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:145:17+38
    assume {:print "$track_exp_sub(28291):", $t26} true;

    // assume Identical($t27, WellFormed($t26)) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:145:17+38
    assume ($t27 == $IsValid'bool'($t26));

    // trace_exp[auto, at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:145:17+38]($t27) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:145:17+38
    assume {:print "$track_exp(28292):", $t27} true;

    // trace_global_mem() at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:145:17+38
    assume {:print "$track_global_mem(29264):", $1_aptos_coin_Delegations_$memory} true;

    // assume WellFormed($t26) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:145:17+38
    assume $IsValid'bool'($t26);

    // $t28 := havoc[val]() at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:145:17+38
    havoc $t28;

    // trace_exp[subauto, at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:145:17+38]($t28) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:145:17+38
    assume {:print "$track_exp_sub(28295):", $t28} true;

    // assume Identical($t29, WellFormed($t28)) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:145:17+38
    assume ($t29 == $IsValid'u64'($t28));

    // trace_exp[auto, at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:145:17+38]($t29) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:145:17+38
    assume {:print "$track_exp(28296):", $t29} true;

    // trace_global_mem() at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:145:17+38
    assume {:print "$track_global_mem(29265):", $1_aptos_coin_Delegations_$memory} true;

    // assume WellFormed($t28) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:145:17+38
    assume $IsValid'u64'($t28);

    // $t30 := havoc[val]() at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:145:17+38
    havoc $t30;

    // trace_exp[subauto, at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:145:17+38]($t30) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:145:17+38
    assume {:print "$track_exp_sub(28299):", $t30} true;

    // assume Identical($t31, WellFormed($t30)) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:145:17+38
    assume ($t31 == $IsValid'u64'($t30));

    // trace_exp[auto, at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:145:17+38]($t31) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:145:17+38
    assume {:print "$track_exp(28300):", $t31} true;

    // trace_global_mem() at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:145:17+38
    assume {:print "$track_global_mem(29266):", $1_aptos_coin_Delegations_$memory} true;

    // assume WellFormed($t30) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:145:17+38
    assume $IsValid'u64'($t30);

    // trace_local[i]($t2) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:145:17+38
    assume {:print "$info(): enter loop, variable(s) i havocked and reassigned"} true;
    assume {:print "$track_local(24,4,2):", $t2} $t2 == $t2;

    // assume Identical($t32, Not(AbortFlag())) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:145:17+38
    assume ($t32 == !$abort_flag);

    // trace_exp[auto, at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:145:17+38]($t32) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:145:17+38
    assume {:print "$track_exp(28302):", $t32} true;

    // trace_global_mem() at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:145:17+38
    assume {:print "$track_global_mem(29267):", $1_aptos_coin_Delegations_$memory} true;

    // assume Not(AbortFlag()) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:145:17+38
    assume {:print "$info(): loop invariant holds at current state"} true;
    assume !$abort_flag;

    // trace_exp[subauto, at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:143:27+1]($t2) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:143:27+1
    assume {:print "$at(2,6048,6049)"} true;
    assume {:print "$track_exp_sub(28307):", $t2} true;

    // trace_exp[subauto, at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:143:37+1]($t2) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:143:37+1
    assume {:print "$track_exp_sub(28308):", $t2} true;

    // trace_exp[subauto, at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:143:42+3]($t13) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:143:42+3
    assume {:print "$track_exp_sub(28309):", $t13} true;

    // assume Identical($t33, And(Ge($t2, 0), Le($t2, $t13))) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:143:17+29
    assume ($t33 == (($t2 >= 0) && ($t2 <= $t13)));

    // trace_exp[auto, at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:143:17+29]($t33) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:143:17+29
    assume {:print "$track_exp(28310):", $t33} true;

    // trace_global_mem() at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:143:17+29
    assume {:print "$track_global_mem(29268):", $1_aptos_coin_Delegations_$memory} true;

    // assume And(Ge($t2, 0), Le($t2, $t13)) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:143:17+29
    assume (($t2 >= 0) && ($t2 <= $t13));

    // trace_exp[subauto, at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:144:42+1]($t2) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:144:42+1
    assume {:print "$at(2,6109,6110)"} true;
    assume {:print "$track_exp_sub(28315):", $t2} true;

    // trace_exp[subauto, at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:144:45+11]($t11) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:144:45+11
    assume {:print "$track_exp_sub(28316):", $t11} true;

    // trace_exp[subauto, at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:144:66+4]($t0) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:144:66+4
    assume {:print "$track_exp_sub(28317):", $t0} true;

    // assume Identical($t34, forall j: Range(0, $t2): Neq<address>(select aptos_coin::DelegatedMintCapability.to(Index($t11, j)), $t0)) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:144:17+54
    assume ($t34 == (var $range_0 := $Range(0, $t2); (forall $i_1: int :: $InRange($range_0, $i_1) ==> (var j := $i_1;
    (!$IsEqual'address'($to#$1_aptos_coin_DelegatedMintCapability(ReadVec($t11, j)), $t0))))));

    // trace_exp[auto, at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:144:17+54]($t34) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:144:17+54
    assume {:print "$track_exp(28318):", $t34} true;

    // trace_global_mem() at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:144:17+54
    assume {:print "$track_global_mem(29269):", $1_aptos_coin_Delegations_$memory} true;

    // assume forall j: Range(0, $t2): Neq<address>(select aptos_coin::DelegatedMintCapability.to(Index($t11, j)), $t0) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:144:17+54
    assume (var $range_0 := $Range(0, $t2); (forall $i_1: int :: $InRange($range_0, $i_1) ==> (var j := $i_1;
    (!$IsEqual'address'($to#$1_aptos_coin_DelegatedMintCapability(ReadVec($t11, j)), $t0)))));

    // trace_exp[subauto, at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:145:48+5]($t14) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:145:48+5
    assume {:print "$at(2,6186,6191)"} true;
    assume {:print "$track_exp_sub(28322):", $t14} true;

    // assume Identical($t35, option::spec_is_none<u64>($t14)) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:145:27+27
    assume ($t35 == $1_option_spec_is_none'u64'($t14));

    // trace_exp[subauto, at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:145:27+27]($t35) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:145:27+27
    assume {:print "$track_exp_sub(28323):", $t35} true;

    // assume Identical($t36, option::spec_is_none<u64>($t14)) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:145:17+38
    assume ($t36 == $1_option_spec_is_none'u64'($t14));

    // trace_exp[auto, at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:145:17+38]($t36) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:145:17+38
    assume {:print "$track_exp(28324):", $t36} true;

    // trace_global_mem() at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:145:17+38
    assume {:print "$track_global_mem(29270):", $1_aptos_coin_Delegations_$memory} true;

    // assume option::spec_is_none<u64>($t14) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:145:17+38
    assume $1_option_spec_is_none'u64'($t14);

    // $t20 := <($t2, $t13) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:147:16+1
    assume {:print "$at(2,6224,6225)"} true;
    call $t20 := $Lt($t2, $t13);

    // if ($t20) goto L1 else goto L0 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:141:9+456
    assume {:print "$at(2,5994,6450)"} true;
    if ($t20) { goto L1; } else { goto L0; }

    // label L1 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:141:9+456
L1:

    // label L2 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:149:42+11
    assume {:print "$at(2,6285,6296)"} true;
L2:

    // $t22 := vector::borrow<aptos_coin::DelegatedMintCapability>($t11, $t2) on_abort goto L8 with $t10 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:149:27+30
    assume {:print "$at(2,6270,6300)"} true;
    call $t22 := $1_vector_borrow'$1_aptos_coin_DelegatedMintCapability'($t11, $t2);
    if ($abort_flag) {
        assume {:print "$at(2,6270,6300)"} true;
        $t10 := $abort_code;
        assume {:print "$track_abort(24,4):", $t10} $t10 == $t10;
        goto L8;
    }

    // $t24 := get_field<aptos_coin::DelegatedMintCapability>.to($t22) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:150:17+10
    assume {:print "$at(2,6318,6328)"} true;
    $t24 := $to#$1_aptos_coin_DelegatedMintCapability($t22);

    // $t26 := ==($t24, $t0) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:150:28+2
    $t26 := $IsEqual'address'($t24, $t0);

    // if ($t26) goto L4 else goto L3 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:150:13+102
    if ($t26) { goto L4; } else { goto L3; }

    // label L4 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:151:17+23
    assume {:print "$at(2,6356,6379)"} true;
L4:

    // $t37 := opaque begin: option::some<u64>($t2) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:151:25+15
    assume {:print "$at(2,6364,6379)"} true;

    // $t38 := copy($t2) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:151:25+15
    $t38 := $t2;

    // assume And(WellFormed($t37), Le(Len<u64>(select option::Option.vec($t37)), 1)) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:151:25+15
    assume ($IsValid'$1_option_Option'u64''($t37) && (LenVec($vec#$1_option_Option'u64'($t37)) <= 1));

    // trace_global_mem() at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:151:25+15
    assume {:print "$track_global_mem(29271):", $1_aptos_coin_Delegations_$memory} true;

    // assume Eq<option::Option<u64>>($t37, option::spec_some<u64>($t38)) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:151:25+15
    assume $IsEqual'$1_option_Option'u64''($t37, $1_option_spec_some'u64'($t38));

    // $t37 := opaque end: option::some<u64>($t2) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:151:25+15

    // $t3 := $t37 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:151:17+5
    $t3 := $t37;

    // trace_local[index]($t37) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:151:17+5
    assume {:print "$track_local(24,4,3):", $t37} $t37 == $t37;

    // goto L0 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:152:17+5
    assume {:print "$at(2,6397,6402)"} true;
    goto L0;

    // label L3 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:154:17+1
    assume {:print "$at(2,6434,6435)"} true;
L3:

    // $t28 := 1 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:154:21+1
    assume {:print "$at(2,6438,6439)"} true;
    $t28 := 1;
    assume $IsValid'u64'($t28);

    // $t30 := +($t2, $t28) on_abort goto L8 with $t10 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:154:19+1
    call $t30 := $AddU64($t2, $t28);
    if ($abort_flag) {
        assume {:print "$at(2,6436,6437)"} true;
        $t10 := $abort_code;
        assume {:print "$track_abort(24,4):", $t10} $t10 == $t10;
        goto L8;
    }

    // trace_local[i]($t30) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:154:13+1
    assume {:print "$track_local(24,4,2):", $t30} $t30 == $t30;

    // goto L6 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:154:22+1
    goto L6;

    // label L0 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:156:9+5
    assume {:print "$at(2,6460,6465)"} true;
L0:

    // trace_return[0]($t3) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:156:9+5
    assume {:print "$at(2,6460,6465)"} true;
    assume {:print "$track_return(24,4,0):", $t3} $t3 == $t3;

    // goto L7 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:156:9+5
    goto L7;

    // label L6 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:156:9+5
    // Loop invariant checking block for the loop started with header: L5
L6:

    // trace_exp[subauto, at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:143:27+1]($t30) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:143:27+1
    assume {:print "$at(2,6048,6049)"} true;
    assume {:print "$track_exp_sub(28329):", $t30} true;

    // trace_exp[subauto, at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:143:37+1]($t30) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:143:37+1
    assume {:print "$track_exp_sub(28330):", $t30} true;

    // trace_exp[subauto, at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:143:42+3]($t13) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:143:42+3
    assume {:print "$track_exp_sub(28331):", $t13} true;

    // assume Identical($t39, And(Ge($t30, 0), Le($t30, $t13))) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:143:17+29
    assume ($t39 == (($t30 >= 0) && ($t30 <= $t13)));

    // trace_exp[auto, at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:143:17+29]($t39) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:143:17+29
    assume {:print "$track_exp(28332):", $t39} true;

    // trace_global_mem() at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:143:17+29
    assume {:print "$track_global_mem(29272):", $1_aptos_coin_Delegations_$memory} true;

    // assert And(Ge($t30, 0), Le($t30, $t13)) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:143:17+29
    assert {:msg "assert_failed(2,6038,6067): induction case of the loop invariant does not hold"}
      (($t30 >= 0) && ($t30 <= $t13));

    // trace_exp[subauto, at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:144:42+1]($t30) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:144:42+1
    assume {:print "$at(2,6109,6110)"} true;
    assume {:print "$track_exp_sub(28337):", $t30} true;

    // trace_exp[subauto, at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:144:45+11]($t11) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:144:45+11
    assume {:print "$track_exp_sub(28338):", $t11} true;

    // trace_exp[subauto, at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:144:66+4]($t0) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:144:66+4
    assume {:print "$track_exp_sub(28339):", $t0} true;

    // assume Identical($t40, forall j: Range(0, $t30): Neq<address>(select aptos_coin::DelegatedMintCapability.to(Index($t11, j)), $t0)) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:144:17+54
    assume ($t40 == (var $range_0 := $Range(0, $t30); (forall $i_1: int :: $InRange($range_0, $i_1) ==> (var j := $i_1;
    (!$IsEqual'address'($to#$1_aptos_coin_DelegatedMintCapability(ReadVec($t11, j)), $t0))))));

    // trace_exp[auto, at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:144:17+54]($t40) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:144:17+54
    assume {:print "$track_exp(28340):", $t40} true;

    // trace_global_mem() at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:144:17+54
    assume {:print "$track_global_mem(29273):", $1_aptos_coin_Delegations_$memory} true;

    // assert forall j: Range(0, $t30): Neq<address>(select aptos_coin::DelegatedMintCapability.to(Index($t11, j)), $t0) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:144:17+54
    assert {:msg "assert_failed(2,6084,6138): induction case of the loop invariant does not hold"}
      (var $range_0 := $Range(0, $t30); (forall $i_1: int :: $InRange($range_0, $i_1) ==> (var j := $i_1;
    (!$IsEqual'address'($to#$1_aptos_coin_DelegatedMintCapability(ReadVec($t11, j)), $t0)))));

    // trace_exp[subauto, at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:145:48+5]($t14) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:145:48+5
    assume {:print "$at(2,6186,6191)"} true;
    assume {:print "$track_exp_sub(28344):", $t14} true;

    // assume Identical($t41, option::spec_is_none<u64>($t14)) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:145:27+27
    assume ($t41 == $1_option_spec_is_none'u64'($t14));

    // trace_exp[subauto, at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:145:27+27]($t41) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:145:27+27
    assume {:print "$track_exp_sub(28345):", $t41} true;

    // assume Identical($t42, option::spec_is_none<u64>($t14)) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:145:17+38
    assume ($t42 == $1_option_spec_is_none'u64'($t14));

    // trace_exp[auto, at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:145:17+38]($t42) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:145:17+38
    assume {:print "$track_exp(28346):", $t42} true;

    // trace_global_mem() at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:145:17+38
    assume {:print "$track_global_mem(29274):", $1_aptos_coin_Delegations_$memory} true;

    // assert option::spec_is_none<u64>($t14) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:145:17+38
    assert {:msg "assert_failed(2,6155,6193): induction case of the loop invariant does not hold"}
      $1_option_spec_is_none'u64'($t14);

    // stop() at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:145:17+38
    assume false;
    return;

    // label L7 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:157:5+1
    assume {:print "$at(2,6470,6471)"} true;
L7:

    // assume Identical($t43, exists[@21]<aptos_coin::Delegations>(0xa550c18)) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:54:20+36
    assume {:print "$at(3,1921,1957)"} true;
    assume ($t43 == $ResourceExists($1_aptos_coin_Delegations_$memory#21, 173345816));

    // trace_exp[subauto, at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:54:20+36]($t43) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:54:20+36
    assume {:print "$track_exp_sub(28209):", $t43} true;

    // assume Identical($t44, Not(exists[@21]<aptos_coin::Delegations>(0xa550c18))) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:54:9+48
    assume ($t44 == !$ResourceExists($1_aptos_coin_Delegations_$memory#21, 173345816));

    // trace_exp[auto, at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:54:9+48]($t44) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:54:9+48
    assume {:print "$track_exp(28210):", $t44} true;

    // trace_global_mem() at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:54:9+48
    assume {:print "$track_global_mem(29275):", $1_aptos_coin_Delegations_$memory} true;

    // assert Not(Not(exists[@21]<aptos_coin::Delegations>(0xa550c18))) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:54:9+48
    assert {:msg "assert_failed(3,1910,1958): function does not abort under this condition"}
      !!$ResourceExists($1_aptos_coin_Delegations_$memory#21, 173345816);

    // trace_exp[subauto, at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:57:37+11]($t7) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:57:37+11
    assume {:print "$at(3,2066,2077)"} true;
    assume {:print "$track_exp_sub(28221):", $t7} true;

    // trace_exp[subauto, at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:57:51+11]($t7) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:57:51+11
    assume {:print "$track_exp_sub(28223):", $t7} true;

    // trace_exp[subauto, at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:57:72+4]($t0) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:57:72+4
    assume {:print "$track_exp_sub(28225):", $t0} true;

    // trace_exp[subauto, at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:58:33+6]($t3) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:58:33+6
    assume {:print "$at(3,2143,2149)"} true;
    assume {:print "$track_exp_sub(28227):", $t3} true;

    // assume Identical($t45, option::spec_borrow<u64>($t3)) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:58:13+27
    assume ($t45 == $1_option_spec_borrow'u64'($t3));

    // trace_exp[subauto, at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:58:13+27]($t45) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:58:13+27
    assume {:print "$track_exp_sub(28228):", $t45} true;

    // trace_exp[subauto, at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:58:69+6]($t3) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:58:69+6
    assume {:print "$track_exp_sub(28230):", $t3} true;

    // assume Identical($t46, option::spec_borrow<u64>($t3)) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:58:49+27
    assume ($t46 == $1_option_spec_borrow'u64'($t3));

    // trace_exp[subauto, at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:58:49+27]($t46) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:58:49+27
    assume {:print "$track_exp_sub(28231):", $t46} true;

    // trace_exp[subauto, at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:58:83+11]($t7) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:58:83+11
    assume {:print "$track_exp_sub(28233):", $t7} true;

    // assume Identical($t47, Implies(exists i: Range(0, Len<aptos_coin::DelegatedMintCapability>($t7)): Eq<address>(select aptos_coin::DelegatedMintCapability.to(Index($t7, i)), $t0), And(Ge(option::spec_borrow<u64>($t3), 0), Lt(option::spec_borrow<u64>($t3), Len<aptos_coin::DelegatedMintCapability>($t7))))) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:57:9+168
    assume {:print "$at(3,2038,2206)"} true;
    assume ($t47 == ((var $range_0 := $Range(0, LenVec($t7)); (exists $i_1: int :: $InRange($range_0, $i_1) && (var i := $i_1;
    ($IsEqual'address'($to#$1_aptos_coin_DelegatedMintCapability(ReadVec($t7, i)), $t0))))) ==> (($1_option_spec_borrow'u64'($t3) >= 0) && ($1_option_spec_borrow'u64'($t3) < LenVec($t7)))));

    // trace_exp[auto, at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:57:9+168]($t47) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:57:9+168
    assume {:print "$track_exp(28234):", $t47} true;

    // trace_global_mem() at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:57:9+168
    assume {:print "$track_global_mem(29276):", $1_aptos_coin_Delegations_$memory} true;

    // assert Implies(exists i: Range(0, Len<aptos_coin::DelegatedMintCapability>($t7)): Eq<address>(select aptos_coin::DelegatedMintCapability.to(Index($t7, i)), $t0), And(Ge(option::spec_borrow<u64>($t3), 0), Lt(option::spec_borrow<u64>($t3), Len<aptos_coin::DelegatedMintCapability>($t7)))) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:57:9+168
    assert {:msg "assert_failed(3,2038,2206): post-condition does not hold"}
      ((var $range_0 := $Range(0, LenVec($t7)); (exists $i_1: int :: $InRange($range_0, $i_1) && (var i := $i_1;
    ($IsEqual'address'($to#$1_aptos_coin_DelegatedMintCapability(ReadVec($t7, i)), $t0))))) ==> (($1_option_spec_borrow'u64'($t3) >= 0) && ($1_option_spec_borrow'u64'($t3) < LenVec($t7))));

    // trace_exp[subauto, at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:59:37+11]($t7) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:59:37+11
    assume {:print "$at(3,2243,2254)"} true;
    assume {:print "$track_exp_sub(28242):", $t7} true;

    // trace_exp[subauto, at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:59:51+11]($t7) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:59:51+11
    assume {:print "$track_exp_sub(28244):", $t7} true;

    // trace_exp[subauto, at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:59:72+4]($t0) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:59:72+4
    assume {:print "$track_exp_sub(28246):", $t0} true;

    // trace_exp[subauto, at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:60:34+6]($t3) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:60:34+6
    assume {:print "$at(3,2321,2327)"} true;
    assume {:print "$track_exp_sub(28248):", $t3} true;

    // assume Identical($t48, option::spec_is_none<u64>($t3)) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:60:13+28
    assume ($t48 == $1_option_spec_is_none'u64'($t3));

    // trace_exp[subauto, at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:60:13+28]($t48) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:60:13+28
    assume {:print "$track_exp_sub(28249):", $t48} true;

    // assume Identical($t49, Implies(forall i: Range(0, Len<aptos_coin::DelegatedMintCapability>($t7)): Neq<address>(select aptos_coin::DelegatedMintCapability.to(Index($t7, i)), $t0), option::spec_is_none<u64>($t3))) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:59:9+114
    assume {:print "$at(3,2215,2329)"} true;
    assume ($t49 == ((var $range_0 := $Range(0, LenVec($t7)); (forall $i_1: int :: $InRange($range_0, $i_1) ==> (var i := $i_1;
    (!$IsEqual'address'($to#$1_aptos_coin_DelegatedMintCapability(ReadVec($t7, i)), $t0))))) ==> $1_option_spec_is_none'u64'($t3)));

    // trace_exp[auto, at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:59:9+114]($t49) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:59:9+114
    assume {:print "$track_exp(28250):", $t49} true;

    // trace_global_mem() at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:59:9+114
    assume {:print "$track_global_mem(29277):", $1_aptos_coin_Delegations_$memory} true;

    // assert Implies(forall i: Range(0, Len<aptos_coin::DelegatedMintCapability>($t7)): Neq<address>(select aptos_coin::DelegatedMintCapability.to(Index($t7, i)), $t0), option::spec_is_none<u64>($t3)) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:59:9+114
    assert {:msg "assert_failed(3,2215,2329): post-condition does not hold"}
      ((var $range_0 := $Range(0, LenVec($t7)); (forall $i_1: int :: $InRange($range_0, $i_1) ==> (var i := $i_1;
    (!$IsEqual'address'($to#$1_aptos_coin_DelegatedMintCapability(ReadVec($t7, i)), $t0))))) ==> $1_option_spec_is_none'u64'($t3));

    // return $t3 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:59:9+114
    $ret0 := $t3;
    return;

    // label L8 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:157:5+1
    assume {:print "$at(2,6470,6471)"} true;
L8:

    // assume Identical($t50, exists[@21]<aptos_coin::Delegations>(0xa550c18)) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:54:20+36
    assume {:print "$at(3,1921,1957)"} true;
    assume ($t50 == $ResourceExists($1_aptos_coin_Delegations_$memory#21, 173345816));

    // trace_exp[subauto, at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:54:20+36]($t50) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:54:20+36
    assume {:print "$track_exp_sub(28209):", $t50} true;

    // assume Identical($t51, Not(exists[@21]<aptos_coin::Delegations>(0xa550c18))) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:54:9+48
    assume ($t51 == !$ResourceExists($1_aptos_coin_Delegations_$memory#21, 173345816));

    // trace_exp[auto, at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:54:9+48]($t51) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:54:9+48
    assume {:print "$track_exp(28210):", $t51} true;

    // trace_global_mem() at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:54:9+48
    assume {:print "$track_global_mem(29278):", $1_aptos_coin_Delegations_$memory} true;

    // assert Not(exists[@21]<aptos_coin::Delegations>(0xa550c18)) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:53:5+484
    assume {:print "$at(3,1851,2335)"} true;
    assert {:msg "assert_failed(3,1851,2335): abort not covered by any of the `aborts_if` clauses"}
      !$ResourceExists($1_aptos_coin_Delegations_$memory#21, 173345816);

    // abort($t10) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.spec.move:53:5+484
    $abort_code := $t10;
    $abort_flag := true;
    return;

}

// fun aptos_coin::has_mint_capability [verification] at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:58:5+120
procedure {:timeLimit 40} $1_aptos_coin_has_mint_capability$verify(_$t0: $signer) returns ($ret0: bool)
{
    // declare local variables
    var $t1: int;
    var $t2: int;
    var $t3: bool;
    var $t0: $signer;
    var $temp_0'bool': bool;
    var $temp_0'signer': $signer;
    $t0 := _$t0;

    // verification entrypoint assumptions
    call $InitVerification();

    // bytecode translation starts here
    // assume WellFormed($t0) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:58:5+1
    assume {:print "$at(2,2064,2065)"} true;
    assume $IsValid'signer'($t0) && $1_signer_is_txn_signer($t0) && $1_signer_is_txn_signer_addr($addr#$signer($t0));

    // assume forall $rsc: ResourceDomain<aptos_coin::MintCapStore>(): WellFormed($rsc) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:58:5+1
    assume (forall $a_0: int :: {$ResourceValue($1_aptos_coin_MintCapStore_$memory, $a_0)}(var $rsc := $ResourceValue($1_aptos_coin_MintCapStore_$memory, $a_0);
    ($IsValid'$1_aptos_coin_MintCapStore'($rsc))));

    // trace_local[account]($t0) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:58:5+1
    assume {:print "$track_local(24,5,0):", $t0} $t0 == $t0;

    // $t1 := signer::address_of($t0) on_abort goto L2 with $t2 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:59:30+27
    assume {:print "$at(2,2150,2177)"} true;
    call $t1 := $1_signer_address_of($t0);
    if ($abort_flag) {
        assume {:print "$at(2,2150,2177)"} true;
        $t2 := $abort_code;
        assume {:print "$track_abort(24,5):", $t2} $t2 == $t2;
        goto L2;
    }

    // $t3 := exists<aptos_coin::MintCapStore>($t1) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:59:9+6
    $t3 := $ResourceExists($1_aptos_coin_MintCapStore_$memory, $t1);

    // trace_return[0]($t3) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:59:9+49
    assume {:print "$track_return(24,5,0):", $t3} $t3 == $t3;

    // label L1 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:60:5+1
    assume {:print "$at(2,2183,2184)"} true;
L1:

    // trace_global_mem() at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:60:5+1
    assume {:print "$at(2,2183,2184)"} true;
    assume {:print "$track_global_mem(29279):", $1_aptos_coin_MintCapStore_$memory} true;

    // assert Not(false) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:60:5+1
    assert {:msg "assert_failed(2,2183,2184): function does not abort under this condition"}
      !false;

    // return $t3 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:60:5+1
    $ret0 := $t3;
    return;

    // label L2 at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:60:5+1
L2:

    // trace_global_mem() at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:60:5+1
    assume {:print "$at(2,2183,2184)"} true;
    assume {:print "$track_global_mem(29280):", $1_aptos_coin_MintCapStore_$memory} true;

    // assert false at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:58:5+120
    assume {:print "$at(2,2064,2184)"} true;
    assert {:msg "assert_failed(2,2064,2184): abort not covered by any of the `aborts_if` clauses"}
      false;

    // abort($t2) at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/sources/aptos_coin.move:58:5+120
    $abort_code := $t2;
    $abort_flag := true;
    return;

}

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/hash.spec.move:7:9+50
function  $1_aptos_hash_spec_keccak256(bytes: Vec (int)): Vec (int);
axiom (forall bytes: Vec (int) ::
(var $$res := $1_aptos_hash_spec_keccak256(bytes);
$IsValid'vec'u8''($$res)));

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/hash.spec.move:12:9+58
function  $1_aptos_hash_spec_sha2_512_internal(bytes: Vec (int)): Vec (int);
axiom (forall bytes: Vec (int) ::
(var $$res := $1_aptos_hash_spec_sha2_512_internal(bytes);
$IsValid'vec'u8''($$res)));

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/hash.spec.move:17:9+58
function  $1_aptos_hash_spec_sha3_512_internal(bytes: Vec (int)): Vec (int);
axiom (forall bytes: Vec (int) ::
(var $$res := $1_aptos_hash_spec_sha3_512_internal(bytes);
$IsValid'vec'u8''($$res)));

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/hash.spec.move:22:9+59
function  $1_aptos_hash_spec_ripemd160_internal(bytes: Vec (int)): Vec (int);
axiom (forall bytes: Vec (int) ::
(var $$res := $1_aptos_hash_spec_ripemd160_internal(bytes);
$IsValid'vec'u8''($$res)));

// spec fun at /home/r/Downloads/Gitrepo/move_bit/aptos-core/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/hash.spec.move:27:9+61
function  $1_aptos_hash_spec_blake2b_256_internal(bytes: Vec (int)): Vec (int);
axiom (forall bytes: Vec (int) ::
(var $$res := $1_aptos_hash_spec_blake2b_256_internal(bytes);
$IsValid'vec'u8''($$res)));
