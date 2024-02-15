// Lean compiler output
// Module: LambdaCalc.semantics
// Imports: Init LambdaCalc.syntax
#include <lean/lean.h>
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#elif defined(__GNUC__) && !defined(__CLANG__)
#pragma GCC diagnostic ignored "-Wunused-parameter"
#pragma GCC diagnostic ignored "-Wunused-label"
#pragma GCC diagnostic ignored "-Wunused-but-set-variable"
#endif
#ifdef __cplusplus
extern "C" {
#endif
static lean_object* l_term_x5b___x3a_x3d___x5d_____closed__2;
static lean_object* l___aux__LambdaCalc__semantics______macroRules__term_x5b___x3a_x3d___x5d____1___closed__7;
static lean_object* l___aux__LambdaCalc__semantics______macroRules__term___x3d_x3d_x3e____1___closed__1;
static lean_object* l_term_x5b___x3a_x3d___x5d_____closed__17;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_object* l___aux__LambdaCalc__semantics______macroRules__term_x5b___x3a_x3d___x5d____1___closed__11;
static lean_object* l_term_x5b___x3a_x3d___x5d_____closed__11;
static lean_object* l_term___x3d_x3d_x3e_____closed__1;
static lean_object* l_term_x5b___x3a_x3d___x5d_____closed__13;
static lean_object* l___aux__LambdaCalc__semantics______macroRules__term___x3d_x3d_x3e____1___closed__4;
static lean_object* l_term_x5b___x3a_x3d___x5d_____closed__4;
static lean_object* l_term_x5b___x3a_x3d___x5d_____closed__9;
static lean_object* l___aux__LambdaCalc__semantics______unexpand__subst__1___lambda__2___closed__1;
static lean_object* l_term___x3d_x3d_x3e_____closed__2;
static lean_object* l_term_x5b___x3a_x3d___x5d_____closed__6;
static lean_object* l___aux__LambdaCalc__semantics______unexpand__subst__1___closed__2;
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___aux__LambdaCalc__semantics______unexpand__subst__1___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
static lean_object* l_term_x5b___x3a_x3d___x5d_____closed__3;
static lean_object* l_term_x5b___x3a_x3d___x5d_____closed__14;
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___aux__LambdaCalc__semantics______unexpand__step__1___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getNumArgs(lean_object*);
static lean_object* l_term_x5b___x3a_x3d___x5d_____closed__18;
LEAN_EXPORT lean_object* l_term___x3d_x3d_x3e__;
static lean_object* l_term_x5b___x3a_x3d___x5d_____closed__12;
LEAN_EXPORT lean_object* l_subst___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l___aux__LambdaCalc__semantics______macroRules__term_x5b___x3a_x3d___x5d____1___closed__1;
static lean_object* l_term___x3d_x3d_x3e_____closed__7;
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
static lean_object* l_term___x3d_x3d_x3e_____closed__4;
lean_object* l_Lean_Syntax_node6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_term_x5b___x3a_x3d___x5d_____closed__15;
static lean_object* l_term_x5b___x3a_x3d___x5d_____closed__5;
static lean_object* l___aux__LambdaCalc__semantics______macroRules__term___x3d_x3d_x3e____1___closed__6;
static lean_object* l___aux__LambdaCalc__semantics______macroRules__term___x3d_x3d_x3e____1___closed__7;
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___aux__LambdaCalc__semantics______unexpand__step__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
static lean_object* l___aux__LambdaCalc__semantics______macroRules__term_x5b___x3a_x3d___x5d____1___closed__5;
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
static lean_object* l___aux__LambdaCalc__semantics______macroRules__term_x5b___x3a_x3d___x5d____1___closed__14;
LEAN_EXPORT lean_object* l_term_x5b___x3a_x3d___x5d__;
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___aux__LambdaCalc__semantics______macroRules__term___x3d_x3d_x3e____1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___aux__LambdaCalc__semantics______unexpand__step__1___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___aux__LambdaCalc__semantics______macroRules__term_x5b___x3a_x3d___x5d____1___closed__12;
static lean_object* l_term___x3d_x3d_x3e_____closed__3;
lean_object* l_Array_append___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___aux__LambdaCalc__semantics______unexpand__subst__1___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_term___x3d_x3d_x3e_____closed__6;
static lean_object* l_term_x5b___x3a_x3d___x5d_____closed__10;
lean_object* l_Array_extract___rarg(lean_object*, lean_object*, lean_object*);
static lean_object* l___aux__LambdaCalc__semantics______unexpand__subst__1___closed__1;
LEAN_EXPORT lean_object* l___aux__LambdaCalc__semantics______unexpand__subst__1___lambda__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_subst(lean_object*, lean_object*, lean_object*);
static lean_object* l___aux__LambdaCalc__semantics______macroRules__term_x5b___x3a_x3d___x5d____1___closed__4;
static lean_object* l___aux__LambdaCalc__semantics______macroRules__term___x3d_x3d_x3e____1___closed__2;
static lean_object* l___aux__LambdaCalc__semantics______macroRules__term_x5b___x3a_x3d___x5d____1___closed__6;
static lean_object* l___aux__LambdaCalc__semantics______macroRules__term_x5b___x3a_x3d___x5d____1___closed__9;
static lean_object* l___aux__LambdaCalc__semantics______macroRules__term_x5b___x3a_x3d___x5d____1___closed__10;
LEAN_EXPORT lean_object* l___aux__LambdaCalc__semantics______macroRules__term_x5b___x3a_x3d___x5d____1(lean_object*, lean_object*, lean_object*);
static lean_object* l___aux__LambdaCalc__semantics______unexpand__subst__1___closed__3;
lean_object* lean_nat_sub(lean_object*, lean_object*);
static lean_object* l___aux__LambdaCalc__semantics______macroRules__term_x5b___x3a_x3d___x5d____1___closed__8;
static lean_object* l_term_x5b___x3a_x3d___x5d_____closed__8;
static lean_object* l_term_x5b___x3a_x3d___x5d_____closed__1;
static lean_object* l___aux__LambdaCalc__semantics______macroRules__term_x5b___x3a_x3d___x5d____1___closed__13;
LEAN_EXPORT lean_object* l___aux__LambdaCalc__semantics______unexpand__subst__1___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_term_x5b___x3a_x3d___x5d_____closed__16;
static lean_object* l_term_x5b___x3a_x3d___x5d_____closed__19;
static lean_object* l___aux__LambdaCalc__semantics______macroRules__term___x3d_x3d_x3e____1___closed__3;
static lean_object* l_term___x3d_x3d_x3e_____closed__5;
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___aux__LambdaCalc__semantics______unexpand__subst__1(lean_object*, lean_object*, lean_object*);
static lean_object* l_term_x5b___x3a_x3d___x5d_____closed__7;
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
static lean_object* l___aux__LambdaCalc__semantics______macroRules__term_x5b___x3a_x3d___x5d____1___closed__2;
static lean_object* l___aux__LambdaCalc__semantics______macroRules__term___x3d_x3d_x3e____1___closed__5;
lean_object* l_String_toSubstring_x27(lean_object*);
static lean_object* l___aux__LambdaCalc__semantics______macroRules__term_x5b___x3a_x3d___x5d____1___closed__3;
LEAN_EXPORT lean_object* l_subst(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
switch (lean_obj_tag(x_3)) {
case 0:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_string_dec_eq(x_1, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
return x_3;
}
else
{
lean_dec(x_3);
lean_inc(x_2);
return x_2;
}
}
case 1:
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_3);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_3, 0);
x_8 = lean_ctor_get(x_3, 1);
x_9 = l_subst(x_1, x_2, x_7);
x_10 = l_subst(x_1, x_2, x_8);
lean_ctor_set(x_3, 1, x_10);
lean_ctor_set(x_3, 0, x_9);
return x_3;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_11 = lean_ctor_get(x_3, 0);
x_12 = lean_ctor_get(x_3, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_3);
x_13 = l_subst(x_1, x_2, x_11);
x_14 = l_subst(x_1, x_2, x_12);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
}
case 2:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_16 = lean_ctor_get(x_3, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_3, 1);
lean_inc(x_17);
x_18 = lean_ctor_get(x_3, 2);
lean_inc(x_18);
x_19 = lean_string_dec_eq(x_1, x_16);
if (x_19 == 0)
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_3);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_3, 2);
lean_dec(x_21);
x_22 = lean_ctor_get(x_3, 1);
lean_dec(x_22);
x_23 = lean_ctor_get(x_3, 0);
lean_dec(x_23);
x_24 = l_subst(x_1, x_2, x_18);
lean_ctor_set(x_3, 2, x_24);
return x_3;
}
else
{
lean_object* x_25; lean_object* x_26; 
lean_dec(x_3);
x_25 = l_subst(x_1, x_2, x_18);
x_26 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_26, 0, x_16);
lean_ctor_set(x_26, 1, x_17);
lean_ctor_set(x_26, 2, x_25);
return x_26;
}
}
else
{
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
return x_3;
}
}
case 3:
{
lean_object* x_27; 
x_27 = lean_box(3);
return x_27;
}
case 4:
{
lean_object* x_28; 
x_28 = lean_box(4);
return x_28;
}
default: 
{
uint8_t x_29; 
x_29 = !lean_is_exclusive(x_3);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_30 = lean_ctor_get(x_3, 0);
x_31 = lean_ctor_get(x_3, 1);
x_32 = lean_ctor_get(x_3, 2);
x_33 = l_subst(x_1, x_2, x_30);
x_34 = l_subst(x_1, x_2, x_31);
x_35 = l_subst(x_1, x_2, x_32);
lean_ctor_set(x_3, 2, x_35);
lean_ctor_set(x_3, 1, x_34);
lean_ctor_set(x_3, 0, x_33);
return x_3;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_36 = lean_ctor_get(x_3, 0);
x_37 = lean_ctor_get(x_3, 1);
x_38 = lean_ctor_get(x_3, 2);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_3);
x_39 = l_subst(x_1, x_2, x_36);
x_40 = l_subst(x_1, x_2, x_37);
x_41 = l_subst(x_1, x_2, x_38);
x_42 = lean_alloc_ctor(5, 3, 0);
lean_ctor_set(x_42, 0, x_39);
lean_ctor_set(x_42, 1, x_40);
lean_ctor_set(x_42, 2, x_41);
return x_42;
}
}
}
}
}
LEAN_EXPORT lean_object* l_subst___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_subst(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
static lean_object* _init_l_term_x5b___x3a_x3d___x5d_____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("term[_:=_]_", 11);
return x_1;
}
}
static lean_object* _init_l_term_x5b___x3a_x3d___x5d_____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_term_x5b___x3a_x3d___x5d_____closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_term_x5b___x3a_x3d___x5d_____closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("andthen", 7);
return x_1;
}
}
static lean_object* _init_l_term_x5b___x3a_x3d___x5d_____closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_term_x5b___x3a_x3d___x5d_____closed__3;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_term_x5b___x3a_x3d___x5d_____closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("[", 1);
return x_1;
}
}
static lean_object* _init_l_term_x5b___x3a_x3d___x5d_____closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_term_x5b___x3a_x3d___x5d_____closed__5;
x_2 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_term_x5b___x3a_x3d___x5d_____closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("term", 4);
return x_1;
}
}
static lean_object* _init_l_term_x5b___x3a_x3d___x5d_____closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_term_x5b___x3a_x3d___x5d_____closed__7;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_term_x5b___x3a_x3d___x5d_____closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_term_x5b___x3a_x3d___x5d_____closed__8;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_term_x5b___x3a_x3d___x5d_____closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_term_x5b___x3a_x3d___x5d_____closed__4;
x_2 = l_term_x5b___x3a_x3d___x5d_____closed__6;
x_3 = l_term_x5b___x3a_x3d___x5d_____closed__9;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_term_x5b___x3a_x3d___x5d_____closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(":=", 2);
return x_1;
}
}
static lean_object* _init_l_term_x5b___x3a_x3d___x5d_____closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_term_x5b___x3a_x3d___x5d_____closed__11;
x_2 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_term_x5b___x3a_x3d___x5d_____closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_term_x5b___x3a_x3d___x5d_____closed__4;
x_2 = l_term_x5b___x3a_x3d___x5d_____closed__10;
x_3 = l_term_x5b___x3a_x3d___x5d_____closed__12;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_term_x5b___x3a_x3d___x5d_____closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_term_x5b___x3a_x3d___x5d_____closed__4;
x_2 = l_term_x5b___x3a_x3d___x5d_____closed__13;
x_3 = l_term_x5b___x3a_x3d___x5d_____closed__9;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_term_x5b___x3a_x3d___x5d_____closed__15() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("]", 1);
return x_1;
}
}
static lean_object* _init_l_term_x5b___x3a_x3d___x5d_____closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_term_x5b___x3a_x3d___x5d_____closed__15;
x_2 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_term_x5b___x3a_x3d___x5d_____closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_term_x5b___x3a_x3d___x5d_____closed__4;
x_2 = l_term_x5b___x3a_x3d___x5d_____closed__14;
x_3 = l_term_x5b___x3a_x3d___x5d_____closed__16;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_term_x5b___x3a_x3d___x5d_____closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_term_x5b___x3a_x3d___x5d_____closed__4;
x_2 = l_term_x5b___x3a_x3d___x5d_____closed__17;
x_3 = l_term_x5b___x3a_x3d___x5d_____closed__9;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_term_x5b___x3a_x3d___x5d_____closed__19() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_term_x5b___x3a_x3d___x5d_____closed__2;
x_2 = lean_unsigned_to_nat(1022u);
x_3 = l_term_x5b___x3a_x3d___x5d_____closed__18;
x_4 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_term_x5b___x3a_x3d___x5d__() {
_start:
{
lean_object* x_1; 
x_1 = l_term_x5b___x3a_x3d___x5d_____closed__19;
return x_1;
}
}
static lean_object* _init_l___aux__LambdaCalc__semantics______macroRules__term_x5b___x3a_x3d___x5d____1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lean", 4);
return x_1;
}
}
static lean_object* _init_l___aux__LambdaCalc__semantics______macroRules__term_x5b___x3a_x3d___x5d____1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Parser", 6);
return x_1;
}
}
static lean_object* _init_l___aux__LambdaCalc__semantics______macroRules__term_x5b___x3a_x3d___x5d____1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Term", 4);
return x_1;
}
}
static lean_object* _init_l___aux__LambdaCalc__semantics______macroRules__term_x5b___x3a_x3d___x5d____1___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("app", 3);
return x_1;
}
}
static lean_object* _init_l___aux__LambdaCalc__semantics______macroRules__term_x5b___x3a_x3d___x5d____1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___aux__LambdaCalc__semantics______macroRules__term_x5b___x3a_x3d___x5d____1___closed__1;
x_2 = l___aux__LambdaCalc__semantics______macroRules__term_x5b___x3a_x3d___x5d____1___closed__2;
x_3 = l___aux__LambdaCalc__semantics______macroRules__term_x5b___x3a_x3d___x5d____1___closed__3;
x_4 = l___aux__LambdaCalc__semantics______macroRules__term_x5b___x3a_x3d___x5d____1___closed__4;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l___aux__LambdaCalc__semantics______macroRules__term_x5b___x3a_x3d___x5d____1___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("subst", 5);
return x_1;
}
}
static lean_object* _init_l___aux__LambdaCalc__semantics______macroRules__term_x5b___x3a_x3d___x5d____1___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___aux__LambdaCalc__semantics______macroRules__term_x5b___x3a_x3d___x5d____1___closed__6;
x_2 = l_String_toSubstring_x27(x_1);
return x_2;
}
}
static lean_object* _init_l___aux__LambdaCalc__semantics______macroRules__term_x5b___x3a_x3d___x5d____1___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___aux__LambdaCalc__semantics______macroRules__term_x5b___x3a_x3d___x5d____1___closed__6;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___aux__LambdaCalc__semantics______macroRules__term_x5b___x3a_x3d___x5d____1___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___aux__LambdaCalc__semantics______macroRules__term_x5b___x3a_x3d___x5d____1___closed__8;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l___aux__LambdaCalc__semantics______macroRules__term_x5b___x3a_x3d___x5d____1___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___aux__LambdaCalc__semantics______macroRules__term_x5b___x3a_x3d___x5d____1___closed__8;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___aux__LambdaCalc__semantics______macroRules__term_x5b___x3a_x3d___x5d____1___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___aux__LambdaCalc__semantics______macroRules__term_x5b___x3a_x3d___x5d____1___closed__10;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l___aux__LambdaCalc__semantics______macroRules__term_x5b___x3a_x3d___x5d____1___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___aux__LambdaCalc__semantics______macroRules__term_x5b___x3a_x3d___x5d____1___closed__9;
x_2 = l___aux__LambdaCalc__semantics______macroRules__term_x5b___x3a_x3d___x5d____1___closed__11;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___aux__LambdaCalc__semantics______macroRules__term_x5b___x3a_x3d___x5d____1___closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("null", 4);
return x_1;
}
}
static lean_object* _init_l___aux__LambdaCalc__semantics______macroRules__term_x5b___x3a_x3d___x5d____1___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___aux__LambdaCalc__semantics______macroRules__term_x5b___x3a_x3d___x5d____1___closed__13;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___aux__LambdaCalc__semantics______macroRules__term_x5b___x3a_x3d___x5d____1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = l_term_x5b___x3a_x3d___x5d_____closed__2;
lean_inc(x_1);
x_5 = l_Lean_Syntax_isOfKind(x_1, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_2);
lean_dec(x_1);
x_6 = lean_box(1);
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_3);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_8 = lean_unsigned_to_nat(1u);
x_9 = l_Lean_Syntax_getArg(x_1, x_8);
x_10 = lean_unsigned_to_nat(3u);
x_11 = l_Lean_Syntax_getArg(x_1, x_10);
x_12 = lean_unsigned_to_nat(5u);
x_13 = l_Lean_Syntax_getArg(x_1, x_12);
lean_dec(x_1);
x_14 = lean_ctor_get(x_2, 5);
lean_inc(x_14);
x_15 = 0;
x_16 = l_Lean_SourceInfo_fromRef(x_14, x_15);
x_17 = lean_ctor_get(x_2, 2);
lean_inc(x_17);
x_18 = lean_ctor_get(x_2, 1);
lean_inc(x_18);
lean_dec(x_2);
x_19 = l___aux__LambdaCalc__semantics______macroRules__term_x5b___x3a_x3d___x5d____1___closed__8;
x_20 = l_Lean_addMacroScope(x_18, x_19, x_17);
x_21 = l___aux__LambdaCalc__semantics______macroRules__term_x5b___x3a_x3d___x5d____1___closed__7;
x_22 = l___aux__LambdaCalc__semantics______macroRules__term_x5b___x3a_x3d___x5d____1___closed__12;
lean_inc(x_16);
x_23 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_23, 0, x_16);
lean_ctor_set(x_23, 1, x_21);
lean_ctor_set(x_23, 2, x_20);
lean_ctor_set(x_23, 3, x_22);
x_24 = l___aux__LambdaCalc__semantics______macroRules__term_x5b___x3a_x3d___x5d____1___closed__14;
lean_inc(x_16);
x_25 = l_Lean_Syntax_node3(x_16, x_24, x_9, x_11, x_13);
x_26 = l___aux__LambdaCalc__semantics______macroRules__term_x5b___x3a_x3d___x5d____1___closed__5;
x_27 = l_Lean_Syntax_node2(x_16, x_26, x_23, x_25);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_3);
return x_28;
}
}
}
LEAN_EXPORT lean_object* l___aux__LambdaCalc__semantics______unexpand__subst__1___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_box(0);
x_5 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
return x_5;
}
}
static lean_object* _init_l___aux__LambdaCalc__semantics______unexpand__subst__1___lambda__2___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___aux__LambdaCalc__semantics______unexpand__subst__1___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_9 = l_Lean_replaceRef(x_1, x_7);
x_10 = 0;
x_11 = l_Lean_SourceInfo_fromRef(x_9, x_10);
x_12 = l_term_x5b___x3a_x3d___x5d_____closed__5;
lean_inc(x_11);
x_13 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
x_14 = l_term_x5b___x3a_x3d___x5d_____closed__11;
lean_inc(x_11);
x_15 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_15, 0, x_11);
lean_ctor_set(x_15, 1, x_14);
x_16 = l_term_x5b___x3a_x3d___x5d_____closed__15;
lean_inc(x_11);
x_17 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_17, 0, x_11);
lean_ctor_set(x_17, 1, x_16);
x_18 = l_term_x5b___x3a_x3d___x5d_____closed__2;
lean_inc(x_11);
x_19 = l_Lean_Syntax_node6(x_11, x_18, x_13, x_3, x_15, x_4, x_17, x_5);
x_20 = l___aux__LambdaCalc__semantics______unexpand__subst__1___lambda__2___closed__1;
x_21 = l_Array_append___rarg(x_20, x_6);
x_22 = l___aux__LambdaCalc__semantics______macroRules__term_x5b___x3a_x3d___x5d____1___closed__14;
lean_inc(x_11);
x_23 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_23, 0, x_11);
lean_ctor_set(x_23, 1, x_22);
lean_ctor_set(x_23, 2, x_21);
x_24 = l_Lean_Syntax_node2(x_11, x_2, x_19, x_23);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_8);
return x_25;
}
}
static lean_object* _init_l___aux__LambdaCalc__semantics______unexpand__subst__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("ident", 5);
return x_1;
}
}
static lean_object* _init_l___aux__LambdaCalc__semantics______unexpand__subst__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___aux__LambdaCalc__semantics______unexpand__subst__1___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___aux__LambdaCalc__semantics______unexpand__subst__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___aux__LambdaCalc__semantics______unexpand__subst__1___lambda__1___boxed), 3, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___aux__LambdaCalc__semantics______unexpand__subst__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = l___aux__LambdaCalc__semantics______macroRules__term_x5b___x3a_x3d___x5d____1___closed__5;
lean_inc(x_1);
x_5 = l_Lean_Syntax_isOfKind(x_1, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_2);
lean_dec(x_1);
x_6 = lean_box(0);
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_3);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_Lean_Syntax_getArg(x_1, x_8);
x_10 = l___aux__LambdaCalc__semantics______unexpand__subst__1___closed__2;
lean_inc(x_9);
x_11 = l_Lean_Syntax_isOfKind(x_9, x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_9);
lean_dec(x_2);
lean_dec(x_1);
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_3);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_14 = lean_unsigned_to_nat(1u);
x_15 = l_Lean_Syntax_getArg(x_1, x_14);
lean_dec(x_1);
x_16 = l___aux__LambdaCalc__semantics______unexpand__subst__1___closed__3;
x_17 = lean_unsigned_to_nat(3u);
lean_inc(x_15);
x_18 = l_Lean_Syntax_matchesNull(x_15, x_17);
if (x_18 == 0)
{
lean_object* x_19; uint8_t x_20; 
x_19 = l_Lean_Syntax_getNumArgs(x_15);
x_20 = lean_nat_dec_le(x_17, x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
lean_dec(x_19);
lean_dec(x_15);
lean_dec(x_9);
x_21 = lean_box(0);
x_22 = lean_apply_3(x_16, x_21, x_2, x_3);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_23 = l_Lean_Syntax_getArg(x_15, x_8);
x_24 = l_Lean_Syntax_getArg(x_15, x_14);
x_25 = lean_unsigned_to_nat(2u);
x_26 = l_Lean_Syntax_getArg(x_15, x_25);
x_27 = l_Lean_Syntax_getArgs(x_15);
lean_dec(x_15);
x_28 = lean_nat_sub(x_19, x_8);
lean_dec(x_19);
x_29 = l_Array_extract___rarg(x_27, x_17, x_28);
lean_dec(x_28);
lean_dec(x_27);
x_30 = lean_box(2);
x_31 = l___aux__LambdaCalc__semantics______macroRules__term_x5b___x3a_x3d___x5d____1___closed__14;
x_32 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
lean_ctor_set(x_32, 2, x_29);
x_33 = l_Lean_Syntax_getArgs(x_32);
lean_dec(x_32);
x_34 = l___aux__LambdaCalc__semantics______unexpand__subst__1___lambda__2(x_9, x_4, x_23, x_24, x_26, x_33, x_2, x_3);
lean_dec(x_2);
lean_dec(x_9);
return x_34;
}
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_35 = l_Lean_Syntax_getArg(x_15, x_8);
x_36 = l_Lean_Syntax_getArg(x_15, x_14);
x_37 = lean_unsigned_to_nat(2u);
x_38 = l_Lean_Syntax_getArg(x_15, x_37);
lean_dec(x_15);
x_39 = l_Lean_replaceRef(x_9, x_2);
lean_dec(x_2);
lean_dec(x_9);
x_40 = 0;
x_41 = l_Lean_SourceInfo_fromRef(x_39, x_40);
x_42 = l_term_x5b___x3a_x3d___x5d_____closed__5;
lean_inc(x_41);
x_43 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
x_44 = l_term_x5b___x3a_x3d___x5d_____closed__11;
lean_inc(x_41);
x_45 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_45, 0, x_41);
lean_ctor_set(x_45, 1, x_44);
x_46 = l_term_x5b___x3a_x3d___x5d_____closed__15;
lean_inc(x_41);
x_47 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_47, 0, x_41);
lean_ctor_set(x_47, 1, x_46);
x_48 = l_term_x5b___x3a_x3d___x5d_____closed__2;
x_49 = l_Lean_Syntax_node6(x_41, x_48, x_43, x_35, x_45, x_36, x_47, x_38);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_3);
return x_50;
}
}
}
}
}
LEAN_EXPORT lean_object* l___aux__LambdaCalc__semantics______unexpand__subst__1___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___aux__LambdaCalc__semantics______unexpand__subst__1___lambda__1(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l___aux__LambdaCalc__semantics______unexpand__subst__1___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___aux__LambdaCalc__semantics______unexpand__subst__1___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_1);
return x_9;
}
}
static lean_object* _init_l_term___x3d_x3d_x3e_____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("term_==>_", 9);
return x_1;
}
}
static lean_object* _init_l_term___x3d_x3d_x3e_____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_term___x3d_x3d_x3e_____closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_term___x3d_x3d_x3e_____closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("==>", 3);
return x_1;
}
}
static lean_object* _init_l_term___x3d_x3d_x3e_____closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_term___x3d_x3d_x3e_____closed__3;
x_2 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_term___x3d_x3d_x3e_____closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_term_x5b___x3a_x3d___x5d_____closed__8;
x_2 = lean_unsigned_to_nat(100u);
x_3 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_term___x3d_x3d_x3e_____closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_term_x5b___x3a_x3d___x5d_____closed__4;
x_2 = l_term___x3d_x3d_x3e_____closed__4;
x_3 = l_term___x3d_x3d_x3e_____closed__5;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_term___x3d_x3d_x3e_____closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_term___x3d_x3d_x3e_____closed__2;
x_2 = lean_unsigned_to_nat(99u);
x_3 = l_term___x3d_x3d_x3e_____closed__6;
x_4 = lean_alloc_ctor(4, 4, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_2);
lean_ctor_set(x_4, 3, x_3);
return x_4;
}
}
static lean_object* _init_l_term___x3d_x3d_x3e__() {
_start:
{
lean_object* x_1; 
x_1 = l_term___x3d_x3d_x3e_____closed__7;
return x_1;
}
}
static lean_object* _init_l___aux__LambdaCalc__semantics______macroRules__term___x3d_x3d_x3e____1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("step", 4);
return x_1;
}
}
static lean_object* _init_l___aux__LambdaCalc__semantics______macroRules__term___x3d_x3d_x3e____1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___aux__LambdaCalc__semantics______macroRules__term___x3d_x3d_x3e____1___closed__1;
x_2 = l_String_toSubstring_x27(x_1);
return x_2;
}
}
static lean_object* _init_l___aux__LambdaCalc__semantics______macroRules__term___x3d_x3d_x3e____1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___aux__LambdaCalc__semantics______macroRules__term___x3d_x3d_x3e____1___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___aux__LambdaCalc__semantics______macroRules__term___x3d_x3d_x3e____1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___aux__LambdaCalc__semantics______macroRules__term___x3d_x3d_x3e____1___closed__3;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l___aux__LambdaCalc__semantics______macroRules__term___x3d_x3d_x3e____1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___aux__LambdaCalc__semantics______macroRules__term___x3d_x3d_x3e____1___closed__3;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___aux__LambdaCalc__semantics______macroRules__term___x3d_x3d_x3e____1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___aux__LambdaCalc__semantics______macroRules__term___x3d_x3d_x3e____1___closed__5;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l___aux__LambdaCalc__semantics______macroRules__term___x3d_x3d_x3e____1___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___aux__LambdaCalc__semantics______macroRules__term___x3d_x3d_x3e____1___closed__4;
x_2 = l___aux__LambdaCalc__semantics______macroRules__term___x3d_x3d_x3e____1___closed__6;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___aux__LambdaCalc__semantics______macroRules__term___x3d_x3d_x3e____1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = l_term___x3d_x3d_x3e_____closed__2;
lean_inc(x_1);
x_5 = l_Lean_Syntax_isOfKind(x_1, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_2);
lean_dec(x_1);
x_6 = lean_box(1);
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_3);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_Lean_Syntax_getArg(x_1, x_8);
x_10 = lean_unsigned_to_nat(2u);
x_11 = l_Lean_Syntax_getArg(x_1, x_10);
lean_dec(x_1);
x_12 = lean_ctor_get(x_2, 5);
lean_inc(x_12);
x_13 = 0;
x_14 = l_Lean_SourceInfo_fromRef(x_12, x_13);
x_15 = lean_ctor_get(x_2, 2);
lean_inc(x_15);
x_16 = lean_ctor_get(x_2, 1);
lean_inc(x_16);
lean_dec(x_2);
x_17 = l___aux__LambdaCalc__semantics______macroRules__term___x3d_x3d_x3e____1___closed__3;
x_18 = l_Lean_addMacroScope(x_16, x_17, x_15);
x_19 = l___aux__LambdaCalc__semantics______macroRules__term___x3d_x3d_x3e____1___closed__2;
x_20 = l___aux__LambdaCalc__semantics______macroRules__term___x3d_x3d_x3e____1___closed__7;
lean_inc(x_14);
x_21 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_21, 0, x_14);
lean_ctor_set(x_21, 1, x_19);
lean_ctor_set(x_21, 2, x_18);
lean_ctor_set(x_21, 3, x_20);
x_22 = l___aux__LambdaCalc__semantics______macroRules__term_x5b___x3a_x3d___x5d____1___closed__14;
lean_inc(x_14);
x_23 = l_Lean_Syntax_node2(x_14, x_22, x_9, x_11);
x_24 = l___aux__LambdaCalc__semantics______macroRules__term_x5b___x3a_x3d___x5d____1___closed__5;
x_25 = l_Lean_Syntax_node2(x_14, x_24, x_21, x_23);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_3);
return x_26;
}
}
}
LEAN_EXPORT lean_object* l___aux__LambdaCalc__semantics______unexpand__step__1___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_8 = l_Lean_replaceRef(x_1, x_6);
x_9 = 0;
x_10 = l_Lean_SourceInfo_fromRef(x_8, x_9);
x_11 = l_term___x3d_x3d_x3e_____closed__3;
lean_inc(x_10);
x_12 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
x_13 = l_term___x3d_x3d_x3e_____closed__2;
lean_inc(x_10);
x_14 = l_Lean_Syntax_node3(x_10, x_13, x_3, x_12, x_4);
x_15 = l___aux__LambdaCalc__semantics______unexpand__subst__1___lambda__2___closed__1;
x_16 = l_Array_append___rarg(x_15, x_5);
x_17 = l___aux__LambdaCalc__semantics______macroRules__term_x5b___x3a_x3d___x5d____1___closed__14;
lean_inc(x_10);
x_18 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_18, 0, x_10);
lean_ctor_set(x_18, 1, x_17);
lean_ctor_set(x_18, 2, x_16);
x_19 = l_Lean_Syntax_node2(x_10, x_2, x_14, x_18);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_7);
return x_20;
}
}
LEAN_EXPORT lean_object* l___aux__LambdaCalc__semantics______unexpand__step__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = l___aux__LambdaCalc__semantics______macroRules__term_x5b___x3a_x3d___x5d____1___closed__5;
lean_inc(x_1);
x_5 = l_Lean_Syntax_isOfKind(x_1, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_2);
lean_dec(x_1);
x_6 = lean_box(0);
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_3);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_Lean_Syntax_getArg(x_1, x_8);
x_10 = l___aux__LambdaCalc__semantics______unexpand__subst__1___closed__2;
lean_inc(x_9);
x_11 = l_Lean_Syntax_isOfKind(x_9, x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_9);
lean_dec(x_2);
lean_dec(x_1);
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_3);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_14 = lean_unsigned_to_nat(1u);
x_15 = l_Lean_Syntax_getArg(x_1, x_14);
lean_dec(x_1);
x_16 = lean_unsigned_to_nat(2u);
lean_inc(x_15);
x_17 = l_Lean_Syntax_matchesNull(x_15, x_16);
if (x_17 == 0)
{
lean_object* x_18; uint8_t x_19; 
x_18 = l_Lean_Syntax_getNumArgs(x_15);
x_19 = lean_nat_dec_le(x_16, x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
lean_dec(x_18);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_2);
x_20 = lean_box(0);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_3);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_22 = l_Lean_Syntax_getArg(x_15, x_8);
x_23 = l_Lean_Syntax_getArg(x_15, x_14);
x_24 = l_Lean_Syntax_getArgs(x_15);
lean_dec(x_15);
x_25 = lean_nat_sub(x_18, x_8);
lean_dec(x_18);
x_26 = l_Array_extract___rarg(x_24, x_16, x_25);
lean_dec(x_25);
lean_dec(x_24);
x_27 = lean_box(2);
x_28 = l___aux__LambdaCalc__semantics______macroRules__term_x5b___x3a_x3d___x5d____1___closed__14;
x_29 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
lean_ctor_set(x_29, 2, x_26);
x_30 = l_Lean_Syntax_getArgs(x_29);
lean_dec(x_29);
x_31 = l___aux__LambdaCalc__semantics______unexpand__step__1___lambda__1(x_9, x_4, x_22, x_23, x_30, x_2, x_3);
lean_dec(x_2);
lean_dec(x_9);
return x_31;
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_32 = l_Lean_Syntax_getArg(x_15, x_8);
x_33 = l_Lean_Syntax_getArg(x_15, x_14);
lean_dec(x_15);
x_34 = l_Lean_replaceRef(x_9, x_2);
lean_dec(x_2);
lean_dec(x_9);
x_35 = 0;
x_36 = l_Lean_SourceInfo_fromRef(x_34, x_35);
x_37 = l_term___x3d_x3d_x3e_____closed__3;
lean_inc(x_36);
x_38 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
x_39 = l_term___x3d_x3d_x3e_____closed__2;
x_40 = l_Lean_Syntax_node3(x_36, x_39, x_32, x_38, x_33);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_3);
return x_41;
}
}
}
}
}
LEAN_EXPORT lean_object* l___aux__LambdaCalc__semantics______unexpand__step__1___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___aux__LambdaCalc__semantics______unexpand__step__1___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_1);
return x_8;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_LambdaCalc_syntax(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_LambdaCalc_semantics(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_LambdaCalc_syntax(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_term_x5b___x3a_x3d___x5d_____closed__1 = _init_l_term_x5b___x3a_x3d___x5d_____closed__1();
lean_mark_persistent(l_term_x5b___x3a_x3d___x5d_____closed__1);
l_term_x5b___x3a_x3d___x5d_____closed__2 = _init_l_term_x5b___x3a_x3d___x5d_____closed__2();
lean_mark_persistent(l_term_x5b___x3a_x3d___x5d_____closed__2);
l_term_x5b___x3a_x3d___x5d_____closed__3 = _init_l_term_x5b___x3a_x3d___x5d_____closed__3();
lean_mark_persistent(l_term_x5b___x3a_x3d___x5d_____closed__3);
l_term_x5b___x3a_x3d___x5d_____closed__4 = _init_l_term_x5b___x3a_x3d___x5d_____closed__4();
lean_mark_persistent(l_term_x5b___x3a_x3d___x5d_____closed__4);
l_term_x5b___x3a_x3d___x5d_____closed__5 = _init_l_term_x5b___x3a_x3d___x5d_____closed__5();
lean_mark_persistent(l_term_x5b___x3a_x3d___x5d_____closed__5);
l_term_x5b___x3a_x3d___x5d_____closed__6 = _init_l_term_x5b___x3a_x3d___x5d_____closed__6();
lean_mark_persistent(l_term_x5b___x3a_x3d___x5d_____closed__6);
l_term_x5b___x3a_x3d___x5d_____closed__7 = _init_l_term_x5b___x3a_x3d___x5d_____closed__7();
lean_mark_persistent(l_term_x5b___x3a_x3d___x5d_____closed__7);
l_term_x5b___x3a_x3d___x5d_____closed__8 = _init_l_term_x5b___x3a_x3d___x5d_____closed__8();
lean_mark_persistent(l_term_x5b___x3a_x3d___x5d_____closed__8);
l_term_x5b___x3a_x3d___x5d_____closed__9 = _init_l_term_x5b___x3a_x3d___x5d_____closed__9();
lean_mark_persistent(l_term_x5b___x3a_x3d___x5d_____closed__9);
l_term_x5b___x3a_x3d___x5d_____closed__10 = _init_l_term_x5b___x3a_x3d___x5d_____closed__10();
lean_mark_persistent(l_term_x5b___x3a_x3d___x5d_____closed__10);
l_term_x5b___x3a_x3d___x5d_____closed__11 = _init_l_term_x5b___x3a_x3d___x5d_____closed__11();
lean_mark_persistent(l_term_x5b___x3a_x3d___x5d_____closed__11);
l_term_x5b___x3a_x3d___x5d_____closed__12 = _init_l_term_x5b___x3a_x3d___x5d_____closed__12();
lean_mark_persistent(l_term_x5b___x3a_x3d___x5d_____closed__12);
l_term_x5b___x3a_x3d___x5d_____closed__13 = _init_l_term_x5b___x3a_x3d___x5d_____closed__13();
lean_mark_persistent(l_term_x5b___x3a_x3d___x5d_____closed__13);
l_term_x5b___x3a_x3d___x5d_____closed__14 = _init_l_term_x5b___x3a_x3d___x5d_____closed__14();
lean_mark_persistent(l_term_x5b___x3a_x3d___x5d_____closed__14);
l_term_x5b___x3a_x3d___x5d_____closed__15 = _init_l_term_x5b___x3a_x3d___x5d_____closed__15();
lean_mark_persistent(l_term_x5b___x3a_x3d___x5d_____closed__15);
l_term_x5b___x3a_x3d___x5d_____closed__16 = _init_l_term_x5b___x3a_x3d___x5d_____closed__16();
lean_mark_persistent(l_term_x5b___x3a_x3d___x5d_____closed__16);
l_term_x5b___x3a_x3d___x5d_____closed__17 = _init_l_term_x5b___x3a_x3d___x5d_____closed__17();
lean_mark_persistent(l_term_x5b___x3a_x3d___x5d_____closed__17);
l_term_x5b___x3a_x3d___x5d_____closed__18 = _init_l_term_x5b___x3a_x3d___x5d_____closed__18();
lean_mark_persistent(l_term_x5b___x3a_x3d___x5d_____closed__18);
l_term_x5b___x3a_x3d___x5d_____closed__19 = _init_l_term_x5b___x3a_x3d___x5d_____closed__19();
lean_mark_persistent(l_term_x5b___x3a_x3d___x5d_____closed__19);
l_term_x5b___x3a_x3d___x5d__ = _init_l_term_x5b___x3a_x3d___x5d__();
lean_mark_persistent(l_term_x5b___x3a_x3d___x5d__);
l___aux__LambdaCalc__semantics______macroRules__term_x5b___x3a_x3d___x5d____1___closed__1 = _init_l___aux__LambdaCalc__semantics______macroRules__term_x5b___x3a_x3d___x5d____1___closed__1();
lean_mark_persistent(l___aux__LambdaCalc__semantics______macroRules__term_x5b___x3a_x3d___x5d____1___closed__1);
l___aux__LambdaCalc__semantics______macroRules__term_x5b___x3a_x3d___x5d____1___closed__2 = _init_l___aux__LambdaCalc__semantics______macroRules__term_x5b___x3a_x3d___x5d____1___closed__2();
lean_mark_persistent(l___aux__LambdaCalc__semantics______macroRules__term_x5b___x3a_x3d___x5d____1___closed__2);
l___aux__LambdaCalc__semantics______macroRules__term_x5b___x3a_x3d___x5d____1___closed__3 = _init_l___aux__LambdaCalc__semantics______macroRules__term_x5b___x3a_x3d___x5d____1___closed__3();
lean_mark_persistent(l___aux__LambdaCalc__semantics______macroRules__term_x5b___x3a_x3d___x5d____1___closed__3);
l___aux__LambdaCalc__semantics______macroRules__term_x5b___x3a_x3d___x5d____1___closed__4 = _init_l___aux__LambdaCalc__semantics______macroRules__term_x5b___x3a_x3d___x5d____1___closed__4();
lean_mark_persistent(l___aux__LambdaCalc__semantics______macroRules__term_x5b___x3a_x3d___x5d____1___closed__4);
l___aux__LambdaCalc__semantics______macroRules__term_x5b___x3a_x3d___x5d____1___closed__5 = _init_l___aux__LambdaCalc__semantics______macroRules__term_x5b___x3a_x3d___x5d____1___closed__5();
lean_mark_persistent(l___aux__LambdaCalc__semantics______macroRules__term_x5b___x3a_x3d___x5d____1___closed__5);
l___aux__LambdaCalc__semantics______macroRules__term_x5b___x3a_x3d___x5d____1___closed__6 = _init_l___aux__LambdaCalc__semantics______macroRules__term_x5b___x3a_x3d___x5d____1___closed__6();
lean_mark_persistent(l___aux__LambdaCalc__semantics______macroRules__term_x5b___x3a_x3d___x5d____1___closed__6);
l___aux__LambdaCalc__semantics______macroRules__term_x5b___x3a_x3d___x5d____1___closed__7 = _init_l___aux__LambdaCalc__semantics______macroRules__term_x5b___x3a_x3d___x5d____1___closed__7();
lean_mark_persistent(l___aux__LambdaCalc__semantics______macroRules__term_x5b___x3a_x3d___x5d____1___closed__7);
l___aux__LambdaCalc__semantics______macroRules__term_x5b___x3a_x3d___x5d____1___closed__8 = _init_l___aux__LambdaCalc__semantics______macroRules__term_x5b___x3a_x3d___x5d____1___closed__8();
lean_mark_persistent(l___aux__LambdaCalc__semantics______macroRules__term_x5b___x3a_x3d___x5d____1___closed__8);
l___aux__LambdaCalc__semantics______macroRules__term_x5b___x3a_x3d___x5d____1___closed__9 = _init_l___aux__LambdaCalc__semantics______macroRules__term_x5b___x3a_x3d___x5d____1___closed__9();
lean_mark_persistent(l___aux__LambdaCalc__semantics______macroRules__term_x5b___x3a_x3d___x5d____1___closed__9);
l___aux__LambdaCalc__semantics______macroRules__term_x5b___x3a_x3d___x5d____1___closed__10 = _init_l___aux__LambdaCalc__semantics______macroRules__term_x5b___x3a_x3d___x5d____1___closed__10();
lean_mark_persistent(l___aux__LambdaCalc__semantics______macroRules__term_x5b___x3a_x3d___x5d____1___closed__10);
l___aux__LambdaCalc__semantics______macroRules__term_x5b___x3a_x3d___x5d____1___closed__11 = _init_l___aux__LambdaCalc__semantics______macroRules__term_x5b___x3a_x3d___x5d____1___closed__11();
lean_mark_persistent(l___aux__LambdaCalc__semantics______macroRules__term_x5b___x3a_x3d___x5d____1___closed__11);
l___aux__LambdaCalc__semantics______macroRules__term_x5b___x3a_x3d___x5d____1___closed__12 = _init_l___aux__LambdaCalc__semantics______macroRules__term_x5b___x3a_x3d___x5d____1___closed__12();
lean_mark_persistent(l___aux__LambdaCalc__semantics______macroRules__term_x5b___x3a_x3d___x5d____1___closed__12);
l___aux__LambdaCalc__semantics______macroRules__term_x5b___x3a_x3d___x5d____1___closed__13 = _init_l___aux__LambdaCalc__semantics______macroRules__term_x5b___x3a_x3d___x5d____1___closed__13();
lean_mark_persistent(l___aux__LambdaCalc__semantics______macroRules__term_x5b___x3a_x3d___x5d____1___closed__13);
l___aux__LambdaCalc__semantics______macroRules__term_x5b___x3a_x3d___x5d____1___closed__14 = _init_l___aux__LambdaCalc__semantics______macroRules__term_x5b___x3a_x3d___x5d____1___closed__14();
lean_mark_persistent(l___aux__LambdaCalc__semantics______macroRules__term_x5b___x3a_x3d___x5d____1___closed__14);
l___aux__LambdaCalc__semantics______unexpand__subst__1___lambda__2___closed__1 = _init_l___aux__LambdaCalc__semantics______unexpand__subst__1___lambda__2___closed__1();
lean_mark_persistent(l___aux__LambdaCalc__semantics______unexpand__subst__1___lambda__2___closed__1);
l___aux__LambdaCalc__semantics______unexpand__subst__1___closed__1 = _init_l___aux__LambdaCalc__semantics______unexpand__subst__1___closed__1();
lean_mark_persistent(l___aux__LambdaCalc__semantics______unexpand__subst__1___closed__1);
l___aux__LambdaCalc__semantics______unexpand__subst__1___closed__2 = _init_l___aux__LambdaCalc__semantics______unexpand__subst__1___closed__2();
lean_mark_persistent(l___aux__LambdaCalc__semantics______unexpand__subst__1___closed__2);
l___aux__LambdaCalc__semantics______unexpand__subst__1___closed__3 = _init_l___aux__LambdaCalc__semantics______unexpand__subst__1___closed__3();
lean_mark_persistent(l___aux__LambdaCalc__semantics______unexpand__subst__1___closed__3);
l_term___x3d_x3d_x3e_____closed__1 = _init_l_term___x3d_x3d_x3e_____closed__1();
lean_mark_persistent(l_term___x3d_x3d_x3e_____closed__1);
l_term___x3d_x3d_x3e_____closed__2 = _init_l_term___x3d_x3d_x3e_____closed__2();
lean_mark_persistent(l_term___x3d_x3d_x3e_____closed__2);
l_term___x3d_x3d_x3e_____closed__3 = _init_l_term___x3d_x3d_x3e_____closed__3();
lean_mark_persistent(l_term___x3d_x3d_x3e_____closed__3);
l_term___x3d_x3d_x3e_____closed__4 = _init_l_term___x3d_x3d_x3e_____closed__4();
lean_mark_persistent(l_term___x3d_x3d_x3e_____closed__4);
l_term___x3d_x3d_x3e_____closed__5 = _init_l_term___x3d_x3d_x3e_____closed__5();
lean_mark_persistent(l_term___x3d_x3d_x3e_____closed__5);
l_term___x3d_x3d_x3e_____closed__6 = _init_l_term___x3d_x3d_x3e_____closed__6();
lean_mark_persistent(l_term___x3d_x3d_x3e_____closed__6);
l_term___x3d_x3d_x3e_____closed__7 = _init_l_term___x3d_x3d_x3e_____closed__7();
lean_mark_persistent(l_term___x3d_x3d_x3e_____closed__7);
l_term___x3d_x3d_x3e__ = _init_l_term___x3d_x3d_x3e__();
lean_mark_persistent(l_term___x3d_x3d_x3e__);
l___aux__LambdaCalc__semantics______macroRules__term___x3d_x3d_x3e____1___closed__1 = _init_l___aux__LambdaCalc__semantics______macroRules__term___x3d_x3d_x3e____1___closed__1();
lean_mark_persistent(l___aux__LambdaCalc__semantics______macroRules__term___x3d_x3d_x3e____1___closed__1);
l___aux__LambdaCalc__semantics______macroRules__term___x3d_x3d_x3e____1___closed__2 = _init_l___aux__LambdaCalc__semantics______macroRules__term___x3d_x3d_x3e____1___closed__2();
lean_mark_persistent(l___aux__LambdaCalc__semantics______macroRules__term___x3d_x3d_x3e____1___closed__2);
l___aux__LambdaCalc__semantics______macroRules__term___x3d_x3d_x3e____1___closed__3 = _init_l___aux__LambdaCalc__semantics______macroRules__term___x3d_x3d_x3e____1___closed__3();
lean_mark_persistent(l___aux__LambdaCalc__semantics______macroRules__term___x3d_x3d_x3e____1___closed__3);
l___aux__LambdaCalc__semantics______macroRules__term___x3d_x3d_x3e____1___closed__4 = _init_l___aux__LambdaCalc__semantics______macroRules__term___x3d_x3d_x3e____1___closed__4();
lean_mark_persistent(l___aux__LambdaCalc__semantics______macroRules__term___x3d_x3d_x3e____1___closed__4);
l___aux__LambdaCalc__semantics______macroRules__term___x3d_x3d_x3e____1___closed__5 = _init_l___aux__LambdaCalc__semantics______macroRules__term___x3d_x3d_x3e____1___closed__5();
lean_mark_persistent(l___aux__LambdaCalc__semantics______macroRules__term___x3d_x3d_x3e____1___closed__5);
l___aux__LambdaCalc__semantics______macroRules__term___x3d_x3d_x3e____1___closed__6 = _init_l___aux__LambdaCalc__semantics______macroRules__term___x3d_x3d_x3e____1___closed__6();
lean_mark_persistent(l___aux__LambdaCalc__semantics______macroRules__term___x3d_x3d_x3e____1___closed__6);
l___aux__LambdaCalc__semantics______macroRules__term___x3d_x3d_x3e____1___closed__7 = _init_l___aux__LambdaCalc__semantics______macroRules__term___x3d_x3d_x3e____1___closed__7();
lean_mark_persistent(l___aux__LambdaCalc__semantics______macroRules__term___x3d_x3d_x3e____1___closed__7);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif