// Lean compiler output
// Module: RiemannHypothesis.Infrastructure.WeightedHilbertSpace
// Imports: Init Mathlib.Analysis.InnerProductSpace.Basic Mathlib.Analysis.InnerProductSpace.l2Space Mathlib.NumberTheory.ArithmeticFunction Mathlib.Data.Nat.Prime.Defs Mathlib.Data.ENNReal.Lemmas Mathlib.Data.Real.Basic Mathlib.Data.Complex.Basic
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
LEAN_EXPORT lean_object* l_PrimeSeq_instSMul___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_PrimeSeq_instAdd(lean_object*);
LEAN_EXPORT lean_object* l_PrimeSeq_instSub___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_PrimeSeq_instZero___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_PrimeSeq_instSub(lean_object*);
LEAN_EXPORT lean_object* l_PrimeSeq_instNeg(lean_object*);
static lean_object* l_PrimeSeq_instCoeFunForallSubtypeNatPrime___closed__1;
LEAN_EXPORT lean_object* l_PrimeSeq_instSMul(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_PrimeSeq_instNeg___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_id___rarg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_PrimeSeq_instZero___rarg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_PrimeSeq_instCoeFunForallSubtypeNatPrime(lean_object*);
LEAN_EXPORT lean_object* l_PrimeSeq_instAdd___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WeightedHilbertSpace_domainH;
LEAN_EXPORT lean_object* l_PrimeSeq_instZero(lean_object*);
static lean_object* _init_l_PrimeSeq_instCoeFunForallSubtypeNatPrime___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_id___rarg___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_PrimeSeq_instCoeFunForallSubtypeNatPrime(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_PrimeSeq_instCoeFunForallSubtypeNatPrime___closed__1;
return x_2;
}
}
LEAN_EXPORT lean_object* l_PrimeSeq_instZero___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_PrimeSeq_instZero(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_PrimeSeq_instZero___rarg___boxed), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_PrimeSeq_instZero___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_PrimeSeq_instZero___rarg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_PrimeSeq_instAdd___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
lean_inc(x_4);
x_5 = lean_apply_1(x_2, x_4);
x_6 = lean_apply_1(x_3, x_4);
x_7 = lean_apply_2(x_1, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_PrimeSeq_instAdd(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_PrimeSeq_instAdd___rarg), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_PrimeSeq_instSMul___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_apply_1(x_3, x_4);
x_6 = lean_apply_2(x_1, x_2, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_PrimeSeq_instSMul(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_PrimeSeq_instSMul___rarg), 4, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_PrimeSeq_instNeg___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_apply_1(x_2, x_3);
x_5 = lean_apply_1(x_1, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_PrimeSeq_instNeg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_PrimeSeq_instNeg___rarg), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_PrimeSeq_instSub___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
lean_inc(x_4);
x_5 = lean_apply_1(x_2, x_4);
x_6 = lean_apply_1(x_3, x_4);
x_7 = lean_apply_2(x_1, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_PrimeSeq_instSub(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_PrimeSeq_instSub___rarg), 4, 0);
return x_2;
}
}
static lean_object* _init_l_WeightedHilbertSpace_domainH() {
_start:
{
return lean_box(0);
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Analysis_InnerProductSpace_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Analysis_InnerProductSpace_l2Space(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_NumberTheory_ArithmeticFunction(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Data_Nat_Prime_Defs(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Data_ENNReal_Lemmas(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Data_Real_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Data_Complex_Basic(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_RiemannHypothesis_Infrastructure_WeightedHilbertSpace(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Analysis_InnerProductSpace_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Analysis_InnerProductSpace_l2Space(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_NumberTheory_ArithmeticFunction(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Data_Nat_Prime_Defs(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Data_ENNReal_Lemmas(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Data_Real_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Data_Complex_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_PrimeSeq_instCoeFunForallSubtypeNatPrime___closed__1 = _init_l_PrimeSeq_instCoeFunForallSubtypeNatPrime___closed__1();
lean_mark_persistent(l_PrimeSeq_instCoeFunForallSubtypeNatPrime___closed__1);
l_WeightedHilbertSpace_domainH = _init_l_WeightedHilbertSpace_domainH();
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
