// Lean compiler output
// Module: ProofsInTheBook.Chapter31
// Imports: public import Init public meta import Init public import Mathlib
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
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_List_finRange(lean_object*);
uint8_t lp_mathlib_Fintype_decidableForallFintype___redArg(lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_proof__in__the__book_ProofsInTheBook_Chapter31_instDecidableIsLeafInPrufer___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_proof__in__the__book_ProofsInTheBook_Chapter31_instDecidableIsLeafInPrufer___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_proof__in__the__book_ProofsInTheBook_Chapter31_instDecidableIsLeafInPrufer(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_proof__in__the__book_ProofsInTheBook_Chapter31_instDecidableIsLeafInPrufer___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_proof__in__the__book_List_filterTR_loop___at___00Multiset_filter___at___00Finset_filter___at___00ProofsInTheBook_Chapter31_pruferLeaves_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_proof__in__the__book_List_filterTR_loop___at___00Multiset_filter___at___00Finset_filter___at___00ProofsInTheBook_Chapter31_pruferLeaves_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_proof__in__the__book_Multiset_filter___at___00Finset_filter___at___00ProofsInTheBook_Chapter31_pruferLeaves_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_proof__in__the__book_Multiset_filter___at___00Finset_filter___at___00ProofsInTheBook_Chapter31_pruferLeaves_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_proof__in__the__book_ProofsInTheBook_Chapter31_pruferLeaves(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_proof__in__the__book_Finset_filter___at___00ProofsInTheBook_Chapter31_pruferLeaves_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_proof__in__the__book_Finset_filter___at___00ProofsInTheBook_Chapter31_pruferLeaves_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_proof__in__the__book_Finset_filter___at___00ProofsInTheBook_Chapter31_pruferLeaves_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_proof__in__the__book_Finset_filter___at___00ProofsInTheBook_Chapter31_pruferLeaves_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_proof__in__the__book_Multiset_filter___at___00Finset_filter___at___00ProofsInTheBook_Chapter31_pruferLeaves_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_proof__in__the__book_Multiset_filter___at___00Finset_filter___at___00ProofsInTheBook_Chapter31_pruferLeaves_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_proof__in__the__book_ProofsInTheBook_Chapter31_instDecidableIsLeafInPrufer___lam__0(lean_object* v_code_1_, lean_object* v_v_2_, lean_object* v_a_3_){
_start:
{
lean_object* v___x_4_; uint8_t v___x_5_; 
v___x_4_ = lean_apply_1(v_code_1_, v_a_3_);
v___x_5_ = lean_nat_dec_eq(v___x_4_, v_v_2_);
lean_dec(v___x_4_);
if (v___x_5_ == 0)
{
uint8_t v___x_6_; 
v___x_6_ = 1;
return v___x_6_;
}
else
{
uint8_t v___x_7_; 
v___x_7_ = 0;
return v___x_7_;
}
}
}
LEAN_EXPORT lean_object* lp_proof__in__the__book_ProofsInTheBook_Chapter31_instDecidableIsLeafInPrufer___lam__0___boxed(lean_object* v_code_8_, lean_object* v_v_9_, lean_object* v_a_10_){
_start:
{
uint8_t v_res_11_; lean_object* v_r_12_; 
v_res_11_ = lp_proof__in__the__book_ProofsInTheBook_Chapter31_instDecidableIsLeafInPrufer___lam__0(v_code_8_, v_v_9_, v_a_10_);
lean_dec(v_v_9_);
v_r_12_ = lean_box(v_res_11_);
return v_r_12_;
}
}
LEAN_EXPORT uint8_t lp_proof__in__the__book_ProofsInTheBook_Chapter31_instDecidableIsLeafInPrufer(lean_object* v_n_13_, lean_object* v_code_14_, lean_object* v_v_15_){
_start:
{
lean_object* v___f_16_; lean_object* v___x_17_; lean_object* v___x_18_; lean_object* v___x_19_; uint8_t v___x_20_; 
v___f_16_ = lean_alloc_closure((void*)(lp_proof__in__the__book_ProofsInTheBook_Chapter31_instDecidableIsLeafInPrufer___lam__0___boxed), 3, 2);
lean_closure_set(v___f_16_, 0, v_code_14_);
lean_closure_set(v___f_16_, 1, v_v_15_);
v___x_17_ = lean_unsigned_to_nat(2u);
v___x_18_ = lean_nat_sub(v_n_13_, v___x_17_);
v___x_19_ = l_List_finRange(v___x_18_);
v___x_20_ = lp_mathlib_Fintype_decidableForallFintype___redArg(v___f_16_, v___x_19_);
return v___x_20_;
}
}
LEAN_EXPORT lean_object* lp_proof__in__the__book_ProofsInTheBook_Chapter31_instDecidableIsLeafInPrufer___boxed(lean_object* v_n_21_, lean_object* v_code_22_, lean_object* v_v_23_){
_start:
{
uint8_t v_res_24_; lean_object* v_r_25_; 
v_res_24_ = lp_proof__in__the__book_ProofsInTheBook_Chapter31_instDecidableIsLeafInPrufer(v_n_21_, v_code_22_, v_v_23_);
lean_dec(v_n_21_);
v_r_25_ = lean_box(v_res_24_);
return v_r_25_;
}
}
LEAN_EXPORT lean_object* lp_proof__in__the__book_List_filterTR_loop___at___00Multiset_filter___at___00Finset_filter___at___00ProofsInTheBook_Chapter31_pruferLeaves_spec__0_spec__0_spec__1(lean_object* v_n_26_, lean_object* v_code_27_, lean_object* v_a_28_, lean_object* v_a_29_){
_start:
{
if (lean_obj_tag(v_a_28_) == 0)
{
lean_object* v___x_30_; 
lean_dec_ref(v_code_27_);
v___x_30_ = l_List_reverse___redArg(v_a_29_);
return v___x_30_;
}
else
{
lean_object* v_head_31_; lean_object* v_tail_32_; lean_object* v___x_34_; uint8_t v_isShared_35_; uint8_t v_isSharedCheck_42_; 
v_head_31_ = lean_ctor_get(v_a_28_, 0);
v_tail_32_ = lean_ctor_get(v_a_28_, 1);
v_isSharedCheck_42_ = !lean_is_exclusive(v_a_28_);
if (v_isSharedCheck_42_ == 0)
{
v___x_34_ = v_a_28_;
v_isShared_35_ = v_isSharedCheck_42_;
goto v_resetjp_33_;
}
else
{
lean_inc(v_tail_32_);
lean_inc(v_head_31_);
lean_dec(v_a_28_);
v___x_34_ = lean_box(0);
v_isShared_35_ = v_isSharedCheck_42_;
goto v_resetjp_33_;
}
v_resetjp_33_:
{
uint8_t v___x_36_; 
lean_inc(v_head_31_);
lean_inc_ref(v_code_27_);
v___x_36_ = lp_proof__in__the__book_ProofsInTheBook_Chapter31_instDecidableIsLeafInPrufer(v_n_26_, v_code_27_, v_head_31_);
if (v___x_36_ == 0)
{
lean_del_object(v___x_34_);
lean_dec(v_head_31_);
v_a_28_ = v_tail_32_;
goto _start;
}
else
{
lean_object* v___x_39_; 
if (v_isShared_35_ == 0)
{
lean_ctor_set(v___x_34_, 1, v_a_29_);
v___x_39_ = v___x_34_;
goto v_reusejp_38_;
}
else
{
lean_object* v_reuseFailAlloc_41_; 
v_reuseFailAlloc_41_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_41_, 0, v_head_31_);
lean_ctor_set(v_reuseFailAlloc_41_, 1, v_a_29_);
v___x_39_ = v_reuseFailAlloc_41_;
goto v_reusejp_38_;
}
v_reusejp_38_:
{
v_a_28_ = v_tail_32_;
v_a_29_ = v___x_39_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* lp_proof__in__the__book_List_filterTR_loop___at___00Multiset_filter___at___00Finset_filter___at___00ProofsInTheBook_Chapter31_pruferLeaves_spec__0_spec__0_spec__1___boxed(lean_object* v_n_43_, lean_object* v_code_44_, lean_object* v_a_45_, lean_object* v_a_46_){
_start:
{
lean_object* v_res_47_; 
v_res_47_ = lp_proof__in__the__book_List_filterTR_loop___at___00Multiset_filter___at___00Finset_filter___at___00ProofsInTheBook_Chapter31_pruferLeaves_spec__0_spec__0_spec__1(v_n_43_, v_code_44_, v_a_45_, v_a_46_);
lean_dec(v_n_43_);
return v_res_47_;
}
}
LEAN_EXPORT lean_object* lp_proof__in__the__book_Multiset_filter___at___00Finset_filter___at___00ProofsInTheBook_Chapter31_pruferLeaves_spec__0_spec__0___redArg(lean_object* v_n_48_, lean_object* v_code_49_, lean_object* v_s_50_){
_start:
{
lean_object* v___x_51_; lean_object* v___x_52_; 
v___x_51_ = lean_box(0);
v___x_52_ = lp_proof__in__the__book_List_filterTR_loop___at___00Multiset_filter___at___00Finset_filter___at___00ProofsInTheBook_Chapter31_pruferLeaves_spec__0_spec__0_spec__1(v_n_48_, v_code_49_, v_s_50_, v___x_51_);
return v___x_52_;
}
}
LEAN_EXPORT lean_object* lp_proof__in__the__book_Multiset_filter___at___00Finset_filter___at___00ProofsInTheBook_Chapter31_pruferLeaves_spec__0_spec__0___redArg___boxed(lean_object* v_n_53_, lean_object* v_code_54_, lean_object* v_s_55_){
_start:
{
lean_object* v_res_56_; 
v_res_56_ = lp_proof__in__the__book_Multiset_filter___at___00Finset_filter___at___00ProofsInTheBook_Chapter31_pruferLeaves_spec__0_spec__0___redArg(v_n_53_, v_code_54_, v_s_55_);
lean_dec(v_n_53_);
return v_res_56_;
}
}
LEAN_EXPORT lean_object* lp_proof__in__the__book_ProofsInTheBook_Chapter31_pruferLeaves(lean_object* v_n_57_, lean_object* v_code_58_){
_start:
{
lean_object* v___x_59_; lean_object* v___x_60_; 
lean_inc(v_n_57_);
v___x_59_ = l_List_finRange(v_n_57_);
v___x_60_ = lp_proof__in__the__book_Multiset_filter___at___00Finset_filter___at___00ProofsInTheBook_Chapter31_pruferLeaves_spec__0_spec__0___redArg(v_n_57_, v_code_58_, v___x_59_);
lean_dec(v_n_57_);
return v___x_60_;
}
}
LEAN_EXPORT lean_object* lp_proof__in__the__book_Finset_filter___at___00ProofsInTheBook_Chapter31_pruferLeaves_spec__0___redArg(lean_object* v_n_61_, lean_object* v_code_62_, lean_object* v_s_63_){
_start:
{
lean_object* v___x_64_; 
v___x_64_ = lp_proof__in__the__book_Multiset_filter___at___00Finset_filter___at___00ProofsInTheBook_Chapter31_pruferLeaves_spec__0_spec__0___redArg(v_n_61_, v_code_62_, v_s_63_);
return v___x_64_;
}
}
LEAN_EXPORT lean_object* lp_proof__in__the__book_Finset_filter___at___00ProofsInTheBook_Chapter31_pruferLeaves_spec__0___redArg___boxed(lean_object* v_n_65_, lean_object* v_code_66_, lean_object* v_s_67_){
_start:
{
lean_object* v_res_68_; 
v_res_68_ = lp_proof__in__the__book_Finset_filter___at___00ProofsInTheBook_Chapter31_pruferLeaves_spec__0___redArg(v_n_65_, v_code_66_, v_s_67_);
lean_dec(v_n_65_);
return v_res_68_;
}
}
LEAN_EXPORT lean_object* lp_proof__in__the__book_Finset_filter___at___00ProofsInTheBook_Chapter31_pruferLeaves_spec__0(lean_object* v_n_69_, lean_object* v_code_70_, lean_object* v_p_71_, lean_object* v_s_72_){
_start:
{
lean_object* v___x_73_; 
v___x_73_ = lp_proof__in__the__book_Multiset_filter___at___00Finset_filter___at___00ProofsInTheBook_Chapter31_pruferLeaves_spec__0_spec__0___redArg(v_n_69_, v_code_70_, v_s_72_);
return v___x_73_;
}
}
LEAN_EXPORT lean_object* lp_proof__in__the__book_Finset_filter___at___00ProofsInTheBook_Chapter31_pruferLeaves_spec__0___boxed(lean_object* v_n_74_, lean_object* v_code_75_, lean_object* v_p_76_, lean_object* v_s_77_){
_start:
{
lean_object* v_res_78_; 
v_res_78_ = lp_proof__in__the__book_Finset_filter___at___00ProofsInTheBook_Chapter31_pruferLeaves_spec__0(v_n_74_, v_code_75_, v_p_76_, v_s_77_);
lean_dec(v_n_74_);
return v_res_78_;
}
}
LEAN_EXPORT lean_object* lp_proof__in__the__book_Multiset_filter___at___00Finset_filter___at___00ProofsInTheBook_Chapter31_pruferLeaves_spec__0_spec__0(lean_object* v_n_79_, lean_object* v_code_80_, lean_object* v_p_81_, lean_object* v_s_82_){
_start:
{
lean_object* v___x_83_; 
v___x_83_ = lp_proof__in__the__book_Multiset_filter___at___00Finset_filter___at___00ProofsInTheBook_Chapter31_pruferLeaves_spec__0_spec__0___redArg(v_n_79_, v_code_80_, v_s_82_);
return v___x_83_;
}
}
LEAN_EXPORT lean_object* lp_proof__in__the__book_Multiset_filter___at___00Finset_filter___at___00ProofsInTheBook_Chapter31_pruferLeaves_spec__0_spec__0___boxed(lean_object* v_n_84_, lean_object* v_code_85_, lean_object* v_p_86_, lean_object* v_s_87_){
_start:
{
lean_object* v_res_88_; 
v_res_88_ = lp_proof__in__the__book_Multiset_filter___at___00Finset_filter___at___00ProofsInTheBook_Chapter31_pruferLeaves_spec__0_spec__0(v_n_84_, v_code_85_, v_p_86_, v_s_87_);
lean_dec(v_n_84_);
return v_res_88_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_proof__in__the__book_ProofsInTheBook_Chapter31(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
