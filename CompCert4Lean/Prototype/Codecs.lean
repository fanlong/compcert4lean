import CompCert4Lean.Prototype.Json

namespace CompCert4Lean.Prototype
open Lean Foundation.Numbers.Rocq.Coq
set_option maxRecDepth 4096
set_option maxHeartbeats 0

mutual
def enc_AST_typ : Nat → Common.AST.typ → CodecResult Json
  | 0, _ => throw "interchange depth exceeded"
  | fuel + 1, value => do
    match value with
    | .Tint => return node "Tint" []
    | .Tfloat => return node "Tfloat" []
    | .Tlong => return node "Tlong" []
    | .Tsingle => return node "Tsingle" []
    | .Tany32 => return node "Tany32" []
    | .Tany64 => return node "Tany64" []

def enc_AST_xtype : Nat → Common.AST.xtype → CodecResult Json
  | 0, _ => throw "interchange depth exceeded"
  | fuel + 1, value => do
    match value with
    | .Xbool => return node "Xbool" []
    | .Xint8signed => return node "Xint8signed" []
    | .Xint8unsigned => return node "Xint8unsigned" []
    | .Xint16signed => return node "Xint16signed" []
    | .Xint16unsigned => return node "Xint16unsigned" []
    | .Xint => return node "Xint" []
    | .Xfloat => return node "Xfloat" []
    | .Xlong => return node "Xlong" []
    | .Xsingle => return node "Xsingle" []
    | .Xptr => return node "Xptr" []
    | .Xany32 => return node "Xany32" []
    | .Xany64 => return node "Xany64" []
    | .Xvoid => return node "Xvoid" []

def enc_AST_calling_convention : Nat → Common.AST.calling_convention → CodecResult Json
  | 0, _ => throw "interchange depth exceeded"
  | fuel + 1, value => do
    return node "AST_calling_convention" [← (encOption (enc_z fuel)) value.cc_vararg, ← (enc_bool fuel) value.cc_unproto, ← (enc_bool fuel) value.cc_structret]

def enc_AST_signature : Nat → Common.AST.signature → CodecResult Json
  | 0, _ => throw "interchange depth exceeded"
  | fuel + 1, value => do
    return node "AST_signature" [← (encList (enc_AST_xtype fuel)) value.sig_args, ← (enc_AST_xtype fuel) value.sig_res, ← (enc_AST_calling_convention fuel) value.sig_cc]

def enc_AST_memory_chunk : Nat → Common.AST.memory_chunk → CodecResult Json
  | 0, _ => throw "interchange depth exceeded"
  | fuel + 1, value => do
    match value with
    | .Mbool => return node "Mbool" []
    | .Mint8signed => return node "Mint8signed" []
    | .Mint8unsigned => return node "Mint8unsigned" []
    | .Mint16signed => return node "Mint16signed" []
    | .Mint16unsigned => return node "Mint16unsigned" []
    | .Mint32 => return node "Mint32" []
    | .Mint64 => return node "Mint64" []
    | .Mfloat32 => return node "Mfloat32" []
    | .Mfloat64 => return node "Mfloat64" []
    | .Many32 => return node "Many32" []
    | .Many64 => return node "Many64" []

def enc_AST_init_data : Nat → Common.AST.init_data → CodecResult Json
  | 0, _ => throw "interchange depth exceeded"
  | fuel + 1, value => do
    match value with
    | .Init_int8 arg0 => return node "Init_int8" [← (enc_int fuel) arg0]
    | .Init_int16 arg0 => return node "Init_int16" [← (enc_int fuel) arg0]
    | .Init_int32 arg0 => return node "Init_int32" [← (enc_int fuel) arg0]
    | .Init_int64 arg0 => return node "Init_int64" [← (enc_long fuel) arg0]
    | .Init_float32 arg0 => return node "Init_float32" [← (enc_single fuel) arg0]
    | .Init_float64 arg0 => return node "Init_float64" [← (enc_float fuel) arg0]
    | .Init_space arg0 => return node "Init_space" [← (enc_z fuel) arg0]
    | .Init_addrof arg0 arg1 => return node "Init_addrof" [← (enc_pos fuel) arg0, ← (enc_ptr fuel) arg1]

def enc_AST_external_function : Nat → Common.AST.external_function → CodecResult Json
  | 0, _ => throw "interchange depth exceeded"
  | fuel + 1, value => do
    match value with
    | .EF_external arg0 arg1 => return node "EF_external" [← (enc_string fuel) arg0, ← (enc_AST_signature fuel) arg1]
    | .EF_builtin arg0 arg1 => return node "EF_builtin" [← (enc_string fuel) arg0, ← (enc_AST_signature fuel) arg1]
    | .EF_runtime arg0 arg1 => return node "EF_runtime" [← (enc_string fuel) arg0, ← (enc_AST_signature fuel) arg1]
    | .EF_vload arg0 => return node "EF_vload" [← (enc_AST_memory_chunk fuel) arg0]
    | .EF_vstore arg0 => return node "EF_vstore" [← (enc_AST_memory_chunk fuel) arg0]
    | .EF_malloc => return node "EF_malloc" []
    | .EF_free => return node "EF_free" []
    | .EF_memcpy arg0 arg1 => return node "EF_memcpy" [← (enc_z fuel) arg0, ← (enc_z fuel) arg1]
    | .EF_annot arg0 arg1 arg2 => return node "EF_annot" [← (enc_pos fuel) arg0, ← (enc_string fuel) arg1, ← (encList (enc_AST_typ fuel)) arg2]
    | .EF_annot_val arg0 arg1 arg2 => return node "EF_annot_val" [← (enc_pos fuel) arg0, ← (enc_string fuel) arg1, ← (enc_AST_typ fuel) arg2]
    | .EF_inline_asm arg0 arg1 arg2 => return node "EF_inline_asm" [← (enc_string fuel) arg0, ← (enc_AST_signature fuel) arg1, ← (encList (enc_string fuel)) arg2]
    | .EF_debug arg0 arg1 arg2 => return node "EF_debug" [← (enc_pos fuel) arg0, ← (enc_pos fuel) arg1, ← (encList (enc_AST_typ fuel)) arg2]

def enc_Ctypes_signedness : Nat → Cfrontend.Ctypes.signedness → CodecResult Json
  | 0, _ => throw "interchange depth exceeded"
  | fuel + 1, value => do
    match value with
    | .Signed => return node "Signed" []
    | .Unsigned => return node "Unsigned" []

def enc_Ctypes_intsize : Nat → Cfrontend.Ctypes.intsize → CodecResult Json
  | 0, _ => throw "interchange depth exceeded"
  | fuel + 1, value => do
    match value with
    | .I8 => return node "I8" []
    | .I16 => return node "I16" []
    | .I32 => return node "I32" []
    | .IBool => return node "IBool" []

def enc_Ctypes_floatsize : Nat → Cfrontend.Ctypes.floatsize → CodecResult Json
  | 0, _ => throw "interchange depth exceeded"
  | fuel + 1, value => do
    match value with
    | .F32 => return node "F32" []
    | .F64 => return node "F64" []

def enc_Ctypes_attr : Nat → Cfrontend.Ctypes.attr → CodecResult Json
  | 0, _ => throw "interchange depth exceeded"
  | fuel + 1, value => do
    return node "Ctypes_attr" [← (enc_bool fuel) value.attr_volatile, ← (encOption (enc_n fuel)) value.attr_alignas]

def enc_Ctypes_coq_type : Nat → Cfrontend.Ctypes.type → CodecResult Json
  | 0, _ => throw "interchange depth exceeded"
  | fuel + 1, value => do
    match value with
    | .Tvoid => return node "Tvoid" []
    | .Tint arg0 arg1 arg2 => return node "Tint" [← (enc_Ctypes_intsize fuel) arg0, ← (enc_Ctypes_signedness fuel) arg1, ← (enc_Ctypes_attr fuel) arg2]
    | .Tlong arg0 arg1 => return node "Tlong" [← (enc_Ctypes_signedness fuel) arg0, ← (enc_Ctypes_attr fuel) arg1]
    | .Tfloat arg0 arg1 => return node "Tfloat" [← (enc_Ctypes_floatsize fuel) arg0, ← (enc_Ctypes_attr fuel) arg1]
    | .Tpointer arg0 arg1 => return node "Tpointer" [← (enc_Ctypes_coq_type fuel) arg0, ← (enc_Ctypes_attr fuel) arg1]
    | .Tarray arg0 arg1 arg2 => return node "Tarray" [← (enc_Ctypes_coq_type fuel) arg0, ← (enc_z fuel) arg1, ← (enc_Ctypes_attr fuel) arg2]
    | .Tfunction arg0 arg1 arg2 => return node "Tfunction" [← (encList (enc_Ctypes_coq_type fuel)) arg0, ← (enc_Ctypes_coq_type fuel) arg1, ← (enc_AST_calling_convention fuel) arg2]
    | .Tstruct arg0 arg1 => return node "Tstruct" [← (enc_pos fuel) arg0, ← (enc_Ctypes_attr fuel) arg1]
    | .Tunion arg0 arg1 => return node "Tunion" [← (enc_pos fuel) arg0, ← (enc_Ctypes_attr fuel) arg1]

def enc_Ctypes_struct_or_union : Nat → Cfrontend.Ctypes.struct_or_union → CodecResult Json
  | 0, _ => throw "interchange depth exceeded"
  | fuel + 1, value => do
    match value with
    | .Struct => return node "Struct" []
    | .Union => return node "Union" []

def enc_Ctypes_member : Nat → Cfrontend.Ctypes.member → CodecResult Json
  | 0, _ => throw "interchange depth exceeded"
  | fuel + 1, value => do
    match value with
    | .Member_plain arg0 arg1 => return node "Member_plain" [← (enc_pos fuel) arg0, ← (enc_Ctypes_coq_type fuel) arg1]
    | .Member_bitfield arg0 arg1 arg2 arg3 arg4 arg5 => return node "Member_bitfield" [← (enc_pos fuel) arg0, ← (enc_Ctypes_intsize fuel) arg1, ← (enc_Ctypes_signedness fuel) arg2, ← (enc_Ctypes_attr fuel) arg3, ← (enc_z fuel) arg4, ← (enc_bool fuel) arg5]

def enc_Ctypes_composite_definition : Nat → Cfrontend.Ctypes.composite_definition → CodecResult Json
  | 0, _ => throw "interchange depth exceeded"
  | fuel + 1, value => do
    match value with
    | .Composite arg0 arg1 arg2 arg3 => return node "Composite" [← (enc_pos fuel) arg0, ← (enc_Ctypes_struct_or_union fuel) arg1, ← (encList (enc_Ctypes_member fuel)) arg2, ← (enc_Ctypes_attr fuel) arg3]

def enc_Ctypes_bitfield : Nat → Cfrontend.Ctypes.bitfield → CodecResult Json
  | 0, _ => throw "interchange depth exceeded"
  | fuel + 1, value => do
    match value with
    | .Full => return node "Full" []
    | .Bits arg0 arg1 arg2 arg3 => return node "Bits" [← (enc_Ctypes_intsize fuel) arg0, ← (enc_Ctypes_signedness fuel) arg1, ← (enc_z fuel) arg2, ← (enc_z fuel) arg3]

def enc_Cop_unary_operation : Nat → Cfrontend.Cop.unary_operation → CodecResult Json
  | 0, _ => throw "interchange depth exceeded"
  | fuel + 1, value => do
    match value with
    | .Onotbool => return node "Onotbool" []
    | .Onotint => return node "Onotint" []
    | .Oneg => return node "Oneg" []
    | .Oabsfloat => return node "Oabsfloat" []

def enc_Cop_binary_operation : Nat → Cfrontend.Cop.binary_operation → CodecResult Json
  | 0, _ => throw "interchange depth exceeded"
  | fuel + 1, value => do
    match value with
    | .Oadd => return node "Oadd" []
    | .Osub => return node "Osub" []
    | .Omul => return node "Omul" []
    | .Odiv => return node "Odiv" []
    | .Omod => return node "Omod" []
    | .Oand => return node "Oand" []
    | .Oor => return node "Oor" []
    | .Oxor => return node "Oxor" []
    | .Oshl => return node "Oshl" []
    | .Oshr => return node "Oshr" []
    | .Oeq => return node "Oeq" []
    | .One => return node "One" []
    | .Olt => return node "Olt" []
    | .Ogt => return node "Ogt" []
    | .Ole => return node "Ole" []
    | .Oge => return node "Oge" []

def enc_Cop_incr_or_decr : Nat → Cfrontend.Cop.incr_or_decr → CodecResult Json
  | 0, _ => throw "interchange depth exceeded"
  | fuel + 1, value => do
    match value with
    | .Incr => return node "Incr" []
    | .Decr => return node "Decr" []

def enc_Values_coq_val : Nat → Common.Values.val → CodecResult Json
  | 0, _ => throw "interchange depth exceeded"
  | fuel + 1, value => do
    match value with
    | .Vundef => return node "Vundef" []
    | .Vint arg0 => return node "Vint" [← (enc_int fuel) arg0]
    | .Vlong arg0 => return node "Vlong" [← (enc_long fuel) arg0]
    | .Vfloat arg0 => return node "Vfloat" [← (enc_float fuel) arg0]
    | .Vsingle arg0 => return node "Vsingle" [← (enc_single fuel) arg0]
    | .Vptr arg0 arg1 => return node "Vptr" [← (enc_pos fuel) arg0, ← (enc_ptr fuel) arg1]

def enc_Csyntax_expr : Nat → Cfrontend.Csyntax.expr → CodecResult Json
  | 0, _ => throw "interchange depth exceeded"
  | fuel + 1, value => do
    match value with
    | .Eval arg0 arg1 => return node "Eval" [← (enc_Values_coq_val fuel) arg0, ← (enc_Ctypes_coq_type fuel) arg1]
    | .Evar arg0 arg1 => return node "Evar" [← (enc_pos fuel) arg0, ← (enc_Ctypes_coq_type fuel) arg1]
    | .Efield arg0 arg1 arg2 => return node "Efield" [← (enc_Csyntax_expr fuel) arg0, ← (enc_pos fuel) arg1, ← (enc_Ctypes_coq_type fuel) arg2]
    | .Evalof arg0 arg1 => return node "Evalof" [← (enc_Csyntax_expr fuel) arg0, ← (enc_Ctypes_coq_type fuel) arg1]
    | .Ederef arg0 arg1 => return node "Ederef" [← (enc_Csyntax_expr fuel) arg0, ← (enc_Ctypes_coq_type fuel) arg1]
    | .Eaddrof arg0 arg1 => return node "Eaddrof" [← (enc_Csyntax_expr fuel) arg0, ← (enc_Ctypes_coq_type fuel) arg1]
    | .Eunop arg0 arg1 arg2 => return node "Eunop" [← (enc_Cop_unary_operation fuel) arg0, ← (enc_Csyntax_expr fuel) arg1, ← (enc_Ctypes_coq_type fuel) arg2]
    | .Ebinop arg0 arg1 arg2 arg3 => return node "Ebinop" [← (enc_Cop_binary_operation fuel) arg0, ← (enc_Csyntax_expr fuel) arg1, ← (enc_Csyntax_expr fuel) arg2, ← (enc_Ctypes_coq_type fuel) arg3]
    | .Ecast arg0 arg1 => return node "Ecast" [← (enc_Csyntax_expr fuel) arg0, ← (enc_Ctypes_coq_type fuel) arg1]
    | .Eseqand arg0 arg1 arg2 => return node "Eseqand" [← (enc_Csyntax_expr fuel) arg0, ← (enc_Csyntax_expr fuel) arg1, ← (enc_Ctypes_coq_type fuel) arg2]
    | .Eseqor arg0 arg1 arg2 => return node "Eseqor" [← (enc_Csyntax_expr fuel) arg0, ← (enc_Csyntax_expr fuel) arg1, ← (enc_Ctypes_coq_type fuel) arg2]
    | .Econdition arg0 arg1 arg2 arg3 => return node "Econdition" [← (enc_Csyntax_expr fuel) arg0, ← (enc_Csyntax_expr fuel) arg1, ← (enc_Csyntax_expr fuel) arg2, ← (enc_Ctypes_coq_type fuel) arg3]
    | .Esizeof arg0 arg1 => return node "Esizeof" [← (enc_Ctypes_coq_type fuel) arg0, ← (enc_Ctypes_coq_type fuel) arg1]
    | .Ealignof arg0 arg1 => return node "Ealignof" [← (enc_Ctypes_coq_type fuel) arg0, ← (enc_Ctypes_coq_type fuel) arg1]
    | .Eassign arg0 arg1 arg2 => return node "Eassign" [← (enc_Csyntax_expr fuel) arg0, ← (enc_Csyntax_expr fuel) arg1, ← (enc_Ctypes_coq_type fuel) arg2]
    | .Eassignop arg0 arg1 arg2 arg3 arg4 => return node "Eassignop" [← (enc_Cop_binary_operation fuel) arg0, ← (enc_Csyntax_expr fuel) arg1, ← (enc_Csyntax_expr fuel) arg2, ← (enc_Ctypes_coq_type fuel) arg3, ← (enc_Ctypes_coq_type fuel) arg4]
    | .Epostincr arg0 arg1 arg2 => return node "Epostincr" [← (enc_Cop_incr_or_decr fuel) arg0, ← (enc_Csyntax_expr fuel) arg1, ← (enc_Ctypes_coq_type fuel) arg2]
    | .Ecomma arg0 arg1 arg2 => return node "Ecomma" [← (enc_Csyntax_expr fuel) arg0, ← (enc_Csyntax_expr fuel) arg1, ← (enc_Ctypes_coq_type fuel) arg2]
    | .Ecall arg0 arg1 arg2 => return node "Ecall" [← (enc_Csyntax_expr fuel) arg0, ← (enc_Csyntax_exprlist fuel) arg1, ← (enc_Ctypes_coq_type fuel) arg2]
    | .Ebuiltin arg0 arg1 arg2 arg3 => return node "Ebuiltin" [← (enc_AST_external_function fuel) arg0, ← (encList (enc_Ctypes_coq_type fuel)) arg1, ← (enc_Csyntax_exprlist fuel) arg2, ← (enc_Ctypes_coq_type fuel) arg3]
    | .Eloc arg0 arg1 arg2 arg3 => return node "Eloc" [← (enc_pos fuel) arg0, ← (enc_ptr fuel) arg1, ← (enc_Ctypes_bitfield fuel) arg2, ← (enc_Ctypes_coq_type fuel) arg3]
    | .Eparen arg0 arg1 arg2 => return node "Eparen" [← (enc_Csyntax_expr fuel) arg0, ← (enc_Ctypes_coq_type fuel) arg1, ← (enc_Ctypes_coq_type fuel) arg2]

def enc_Csyntax_exprlist : Nat → Cfrontend.Csyntax.exprlist → CodecResult Json
  | 0, _ => throw "interchange depth exceeded"
  | fuel + 1, value => do
    match value with
    | .Enil => return node "Enil" []
    | .Econs arg0 arg1 => return node "Econs" [← (enc_Csyntax_expr fuel) arg0, ← (enc_Csyntax_exprlist fuel) arg1]

def enc_Csyntax_statement : Nat → Cfrontend.Csyntax.statement → CodecResult Json
  | 0, _ => throw "interchange depth exceeded"
  | fuel + 1, value => do
    match value with
    | .Sskip => return node "Sskip" []
    | .Sdo arg0 => return node "Sdo" [← (enc_Csyntax_expr fuel) arg0]
    | .Ssequence arg0 arg1 => return node "Ssequence" [← (enc_Csyntax_statement fuel) arg0, ← (enc_Csyntax_statement fuel) arg1]
    | .Sifthenelse arg0 arg1 arg2 => return node "Sifthenelse" [← (enc_Csyntax_expr fuel) arg0, ← (enc_Csyntax_statement fuel) arg1, ← (enc_Csyntax_statement fuel) arg2]
    | .Swhile arg0 arg1 => return node "Swhile" [← (enc_Csyntax_expr fuel) arg0, ← (enc_Csyntax_statement fuel) arg1]
    | .Sdowhile arg0 arg1 => return node "Sdowhile" [← (enc_Csyntax_expr fuel) arg0, ← (enc_Csyntax_statement fuel) arg1]
    | .Sfor arg0 arg1 arg2 arg3 => return node "Sfor" [← (enc_Csyntax_statement fuel) arg0, ← (enc_Csyntax_expr fuel) arg1, ← (enc_Csyntax_statement fuel) arg2, ← (enc_Csyntax_statement fuel) arg3]
    | .Sbreak => return node "Sbreak" []
    | .Scontinue => return node "Scontinue" []
    | .Sreturn arg0 => return node "Sreturn" [← (encOption (enc_Csyntax_expr fuel)) arg0]
    | .Sswitch arg0 arg1 => return node "Sswitch" [← (enc_Csyntax_expr fuel) arg0, ← (enc_Csyntax_labeled_statements fuel) arg1]
    | .Slabel arg0 arg1 => return node "Slabel" [← (enc_pos fuel) arg0, ← (enc_Csyntax_statement fuel) arg1]
    | .Sgoto arg0 => return node "Sgoto" [← (enc_pos fuel) arg0]

def enc_Csyntax_labeled_statements : Nat → Cfrontend.Csyntax.labeled_statements → CodecResult Json
  | 0, _ => throw "interchange depth exceeded"
  | fuel + 1, value => do
    match value with
    | .LSnil => return node "LSnil" []
    | .LScons arg0 arg1 arg2 => return node "LScons" [← (encOption (enc_z fuel)) arg0, ← (enc_Csyntax_statement fuel) arg1, ← (enc_Csyntax_labeled_statements fuel) arg2]

def enc_Csyntax_coq_function : Nat → Cfrontend.Csyntax.function → CodecResult Json
  | 0, _ => throw "interchange depth exceeded"
  | fuel + 1, value => do
    return node "Csyntax_coq_function" [← (enc_Ctypes_coq_type fuel) value.fn_return, ← (enc_AST_calling_convention fuel) value.fn_callconv, ← (encList (encPair (enc_pos fuel) (enc_Ctypes_coq_type fuel))) value.fn_params, ← (encList (encPair (enc_pos fuel) (enc_Ctypes_coq_type fuel))) value.fn_vars, ← (enc_Csyntax_statement fuel) value.fn_body]

def enc_Asm_ireg : Nat → X86.Asm.ireg → CodecResult Json
  | 0, _ => throw "interchange depth exceeded"
  | fuel + 1, value => do
    match value with
    | .RAX => return node "RAX" []
    | .RBX => return node "RBX" []
    | .RCX => return node "RCX" []
    | .RDX => return node "RDX" []
    | .RSI => return node "RSI" []
    | .RDI => return node "RDI" []
    | .RBP => return node "RBP" []
    | .RSP => return node "RSP" []
    | .R8 => return node "R8" []
    | .R9 => return node "R9" []
    | .R10 => return node "R10" []
    | .R11 => return node "R11" []
    | .R12 => return node "R12" []
    | .R13 => return node "R13" []
    | .R14 => return node "R14" []
    | .R15 => return node "R15" []

def enc_Asm_freg : Nat → X86.Asm.freg → CodecResult Json
  | 0, _ => throw "interchange depth exceeded"
  | fuel + 1, value => do
    match value with
    | .XMM0 => return node "XMM0" []
    | .XMM1 => return node "XMM1" []
    | .XMM2 => return node "XMM2" []
    | .XMM3 => return node "XMM3" []
    | .XMM4 => return node "XMM4" []
    | .XMM5 => return node "XMM5" []
    | .XMM6 => return node "XMM6" []
    | .XMM7 => return node "XMM7" []
    | .XMM8 => return node "XMM8" []
    | .XMM9 => return node "XMM9" []
    | .XMM10 => return node "XMM10" []
    | .XMM11 => return node "XMM11" []
    | .XMM12 => return node "XMM12" []
    | .XMM13 => return node "XMM13" []
    | .XMM14 => return node "XMM14" []
    | .XMM15 => return node "XMM15" []

def enc_Asm_crbit : Nat → X86.Asm.crbit → CodecResult Json
  | 0, _ => throw "interchange depth exceeded"
  | fuel + 1, value => do
    match value with
    | .ZF => return node "ZF" []
    | .CF => return node "CF" []
    | .PF => return node "PF" []
    | .SF => return node "SF" []
    | .OF => return node "OF" []

def enc_Asm_preg : Nat → X86.Asm.preg → CodecResult Json
  | 0, _ => throw "interchange depth exceeded"
  | fuel + 1, value => do
    match value with
    | .PC => return node "PC" []
    | .IR arg0 => return node "IR" [← (enc_Asm_ireg fuel) arg0]
    | .FR arg0 => return node "FR" [← (enc_Asm_freg fuel) arg0]
    | .ST0 => return node "ST0" []
    | .CR arg0 => return node "CR" [← (enc_Asm_crbit fuel) arg0]
    | .RA => return node "RA" []

def enc_Asm_addrmode : Nat → X86.Asm.addrmode → CodecResult Json
  | 0, _ => throw "interchange depth exceeded"
  | fuel + 1, value => do
    match value with
    | .Addrmode arg0 arg1 arg2 => return node "Addrmode" [← (encOption (enc_Asm_ireg fuel)) arg0, ← (encOption (encPair (enc_Asm_ireg fuel) (enc_z fuel))) arg1, ← (encSum (enc_z fuel) (encPair (enc_pos fuel) (enc_ptr fuel))) arg2]

def enc_Asm_testcond : Nat → X86.Asm.testcond → CodecResult Json
  | 0, _ => throw "interchange depth exceeded"
  | fuel + 1, value => do
    match value with
    | .Cond_e => return node "Cond_e" []
    | .Cond_ne => return node "Cond_ne" []
    | .Cond_b => return node "Cond_b" []
    | .Cond_be => return node "Cond_be" []
    | .Cond_ae => return node "Cond_ae" []
    | .Cond_a => return node "Cond_a" []
    | .Cond_l => return node "Cond_l" []
    | .Cond_le => return node "Cond_le" []
    | .Cond_ge => return node "Cond_ge" []
    | .Cond_g => return node "Cond_g" []
    | .Cond_p => return node "Cond_p" []
    | .Cond_np => return node "Cond_np" []

def enc_Asm_instruction : Nat → X86.Asm.instruction → CodecResult Json
  | 0, _ => throw "interchange depth exceeded"
  | fuel + 1, value => do
    match value with
    | .Pmov_rr arg0 arg1 => return node "Pmov_rr" [← (enc_Asm_ireg fuel) arg0, ← (enc_Asm_ireg fuel) arg1]
    | .Pmovl_ri arg0 arg1 => return node "Pmovl_ri" [← (enc_Asm_ireg fuel) arg0, ← (enc_int fuel) arg1]
    | .Pmovq_ri arg0 arg1 => return node "Pmovq_ri" [← (enc_Asm_ireg fuel) arg0, ← (enc_long fuel) arg1]
    | .Pmov_rs arg0 arg1 => return node "Pmov_rs" [← (enc_Asm_ireg fuel) arg0, ← (enc_pos fuel) arg1]
    | .Pmovl_rm arg0 arg1 => return node "Pmovl_rm" [← (enc_Asm_ireg fuel) arg0, ← (enc_Asm_addrmode fuel) arg1]
    | .Pmovq_rm arg0 arg1 => return node "Pmovq_rm" [← (enc_Asm_ireg fuel) arg0, ← (enc_Asm_addrmode fuel) arg1]
    | .Pmovl_mr arg0 arg1 => return node "Pmovl_mr" [← (enc_Asm_addrmode fuel) arg0, ← (enc_Asm_ireg fuel) arg1]
    | .Pmovq_mr arg0 arg1 => return node "Pmovq_mr" [← (enc_Asm_addrmode fuel) arg0, ← (enc_Asm_ireg fuel) arg1]
    | .Pmovsd_ff arg0 arg1 => return node "Pmovsd_ff" [← (enc_Asm_freg fuel) arg0, ← (enc_Asm_freg fuel) arg1]
    | .Pmovsd_fi arg0 arg1 => return node "Pmovsd_fi" [← (enc_Asm_freg fuel) arg0, ← (enc_float fuel) arg1]
    | .Pmovsd_fm arg0 arg1 => return node "Pmovsd_fm" [← (enc_Asm_freg fuel) arg0, ← (enc_Asm_addrmode fuel) arg1]
    | .Pmovsd_mf arg0 arg1 => return node "Pmovsd_mf" [← (enc_Asm_addrmode fuel) arg0, ← (enc_Asm_freg fuel) arg1]
    | .Pmovss_fi arg0 arg1 => return node "Pmovss_fi" [← (enc_Asm_freg fuel) arg0, ← (enc_single fuel) arg1]
    | .Pmovss_fm arg0 arg1 => return node "Pmovss_fm" [← (enc_Asm_freg fuel) arg0, ← (enc_Asm_addrmode fuel) arg1]
    | .Pmovss_mf arg0 arg1 => return node "Pmovss_mf" [← (enc_Asm_addrmode fuel) arg0, ← (enc_Asm_freg fuel) arg1]
    | .Pfldl_m arg0 => return node "Pfldl_m" [← (enc_Asm_addrmode fuel) arg0]
    | .Pfstpl_m arg0 => return node "Pfstpl_m" [← (enc_Asm_addrmode fuel) arg0]
    | .Pflds_m arg0 => return node "Pflds_m" [← (enc_Asm_addrmode fuel) arg0]
    | .Pfstps_m arg0 => return node "Pfstps_m" [← (enc_Asm_addrmode fuel) arg0]
    | .Pmovb_mr arg0 arg1 => return node "Pmovb_mr" [← (enc_Asm_addrmode fuel) arg0, ← (enc_Asm_ireg fuel) arg1]
    | .Pmovw_mr arg0 arg1 => return node "Pmovw_mr" [← (enc_Asm_addrmode fuel) arg0, ← (enc_Asm_ireg fuel) arg1]
    | .Pmovzb_rr arg0 arg1 => return node "Pmovzb_rr" [← (enc_Asm_ireg fuel) arg0, ← (enc_Asm_ireg fuel) arg1]
    | .Pmovzb_rm arg0 arg1 => return node "Pmovzb_rm" [← (enc_Asm_ireg fuel) arg0, ← (enc_Asm_addrmode fuel) arg1]
    | .Pmovsb_rr arg0 arg1 => return node "Pmovsb_rr" [← (enc_Asm_ireg fuel) arg0, ← (enc_Asm_ireg fuel) arg1]
    | .Pmovsb_rm arg0 arg1 => return node "Pmovsb_rm" [← (enc_Asm_ireg fuel) arg0, ← (enc_Asm_addrmode fuel) arg1]
    | .Pmovzw_rr arg0 arg1 => return node "Pmovzw_rr" [← (enc_Asm_ireg fuel) arg0, ← (enc_Asm_ireg fuel) arg1]
    | .Pmovzw_rm arg0 arg1 => return node "Pmovzw_rm" [← (enc_Asm_ireg fuel) arg0, ← (enc_Asm_addrmode fuel) arg1]
    | .Pmovsw_rr arg0 arg1 => return node "Pmovsw_rr" [← (enc_Asm_ireg fuel) arg0, ← (enc_Asm_ireg fuel) arg1]
    | .Pmovsw_rm arg0 arg1 => return node "Pmovsw_rm" [← (enc_Asm_ireg fuel) arg0, ← (enc_Asm_addrmode fuel) arg1]
    | .Pmovzl_rr arg0 arg1 => return node "Pmovzl_rr" [← (enc_Asm_ireg fuel) arg0, ← (enc_Asm_ireg fuel) arg1]
    | .Pmovsl_rr arg0 arg1 => return node "Pmovsl_rr" [← (enc_Asm_ireg fuel) arg0, ← (enc_Asm_ireg fuel) arg1]
    | .Pmovls_rr arg0 => return node "Pmovls_rr" [← (enc_Asm_ireg fuel) arg0]
    | .Pcvtsd2ss_ff arg0 arg1 => return node "Pcvtsd2ss_ff" [← (enc_Asm_freg fuel) arg0, ← (enc_Asm_freg fuel) arg1]
    | .Pcvtss2sd_ff arg0 arg1 => return node "Pcvtss2sd_ff" [← (enc_Asm_freg fuel) arg0, ← (enc_Asm_freg fuel) arg1]
    | .Pcvttsd2si_rf arg0 arg1 => return node "Pcvttsd2si_rf" [← (enc_Asm_ireg fuel) arg0, ← (enc_Asm_freg fuel) arg1]
    | .Pcvtsi2sd_fr arg0 arg1 => return node "Pcvtsi2sd_fr" [← (enc_Asm_freg fuel) arg0, ← (enc_Asm_ireg fuel) arg1]
    | .Pcvttss2si_rf arg0 arg1 => return node "Pcvttss2si_rf" [← (enc_Asm_ireg fuel) arg0, ← (enc_Asm_freg fuel) arg1]
    | .Pcvtsi2ss_fr arg0 arg1 => return node "Pcvtsi2ss_fr" [← (enc_Asm_freg fuel) arg0, ← (enc_Asm_ireg fuel) arg1]
    | .Pcvttsd2sl_rf arg0 arg1 => return node "Pcvttsd2sl_rf" [← (enc_Asm_ireg fuel) arg0, ← (enc_Asm_freg fuel) arg1]
    | .Pcvtsl2sd_fr arg0 arg1 => return node "Pcvtsl2sd_fr" [← (enc_Asm_freg fuel) arg0, ← (enc_Asm_ireg fuel) arg1]
    | .Pcvttss2sl_rf arg0 arg1 => return node "Pcvttss2sl_rf" [← (enc_Asm_ireg fuel) arg0, ← (enc_Asm_freg fuel) arg1]
    | .Pcvtsl2ss_fr arg0 arg1 => return node "Pcvtsl2ss_fr" [← (enc_Asm_freg fuel) arg0, ← (enc_Asm_ireg fuel) arg1]
    | .Pleal arg0 arg1 => return node "Pleal" [← (enc_Asm_ireg fuel) arg0, ← (enc_Asm_addrmode fuel) arg1]
    | .Pleaq arg0 arg1 => return node "Pleaq" [← (enc_Asm_ireg fuel) arg0, ← (enc_Asm_addrmode fuel) arg1]
    | .Pnegl arg0 => return node "Pnegl" [← (enc_Asm_ireg fuel) arg0]
    | .Pnegq arg0 => return node "Pnegq" [← (enc_Asm_ireg fuel) arg0]
    | .Paddl_ri arg0 arg1 => return node "Paddl_ri" [← (enc_Asm_ireg fuel) arg0, ← (enc_int fuel) arg1]
    | .Paddq_ri arg0 arg1 => return node "Paddq_ri" [← (enc_Asm_ireg fuel) arg0, ← (enc_long fuel) arg1]
    | .Psubl_rr arg0 arg1 => return node "Psubl_rr" [← (enc_Asm_ireg fuel) arg0, ← (enc_Asm_ireg fuel) arg1]
    | .Psubq_rr arg0 arg1 => return node "Psubq_rr" [← (enc_Asm_ireg fuel) arg0, ← (enc_Asm_ireg fuel) arg1]
    | .Pimull_rr arg0 arg1 => return node "Pimull_rr" [← (enc_Asm_ireg fuel) arg0, ← (enc_Asm_ireg fuel) arg1]
    | .Pimulq_rr arg0 arg1 => return node "Pimulq_rr" [← (enc_Asm_ireg fuel) arg0, ← (enc_Asm_ireg fuel) arg1]
    | .Pimull_ri arg0 arg1 => return node "Pimull_ri" [← (enc_Asm_ireg fuel) arg0, ← (enc_int fuel) arg1]
    | .Pimulq_ri arg0 arg1 => return node "Pimulq_ri" [← (enc_Asm_ireg fuel) arg0, ← (enc_long fuel) arg1]
    | .Pimull_r arg0 => return node "Pimull_r" [← (enc_Asm_ireg fuel) arg0]
    | .Pimulq_r arg0 => return node "Pimulq_r" [← (enc_Asm_ireg fuel) arg0]
    | .Pmull_r arg0 => return node "Pmull_r" [← (enc_Asm_ireg fuel) arg0]
    | .Pmulq_r arg0 => return node "Pmulq_r" [← (enc_Asm_ireg fuel) arg0]
    | .Pcltd => return node "Pcltd" []
    | .Pcqto => return node "Pcqto" []
    | .Pdivl arg0 => return node "Pdivl" [← (enc_Asm_ireg fuel) arg0]
    | .Pdivq arg0 => return node "Pdivq" [← (enc_Asm_ireg fuel) arg0]
    | .Pidivl arg0 => return node "Pidivl" [← (enc_Asm_ireg fuel) arg0]
    | .Pidivq arg0 => return node "Pidivq" [← (enc_Asm_ireg fuel) arg0]
    | .Pandl_rr arg0 arg1 => return node "Pandl_rr" [← (enc_Asm_ireg fuel) arg0, ← (enc_Asm_ireg fuel) arg1]
    | .Pandq_rr arg0 arg1 => return node "Pandq_rr" [← (enc_Asm_ireg fuel) arg0, ← (enc_Asm_ireg fuel) arg1]
    | .Pandl_ri arg0 arg1 => return node "Pandl_ri" [← (enc_Asm_ireg fuel) arg0, ← (enc_int fuel) arg1]
    | .Pandq_ri arg0 arg1 => return node "Pandq_ri" [← (enc_Asm_ireg fuel) arg0, ← (enc_long fuel) arg1]
    | .Porl_rr arg0 arg1 => return node "Porl_rr" [← (enc_Asm_ireg fuel) arg0, ← (enc_Asm_ireg fuel) arg1]
    | .Porq_rr arg0 arg1 => return node "Porq_rr" [← (enc_Asm_ireg fuel) arg0, ← (enc_Asm_ireg fuel) arg1]
    | .Porl_ri arg0 arg1 => return node "Porl_ri" [← (enc_Asm_ireg fuel) arg0, ← (enc_int fuel) arg1]
    | .Porq_ri arg0 arg1 => return node "Porq_ri" [← (enc_Asm_ireg fuel) arg0, ← (enc_long fuel) arg1]
    | .Pxorl_r arg0 => return node "Pxorl_r" [← (enc_Asm_ireg fuel) arg0]
    | .Pxorq_r arg0 => return node "Pxorq_r" [← (enc_Asm_ireg fuel) arg0]
    | .Pxorl_rr arg0 arg1 => return node "Pxorl_rr" [← (enc_Asm_ireg fuel) arg0, ← (enc_Asm_ireg fuel) arg1]
    | .Pxorq_rr arg0 arg1 => return node "Pxorq_rr" [← (enc_Asm_ireg fuel) arg0, ← (enc_Asm_ireg fuel) arg1]
    | .Pxorl_ri arg0 arg1 => return node "Pxorl_ri" [← (enc_Asm_ireg fuel) arg0, ← (enc_int fuel) arg1]
    | .Pxorq_ri arg0 arg1 => return node "Pxorq_ri" [← (enc_Asm_ireg fuel) arg0, ← (enc_long fuel) arg1]
    | .Pnotl arg0 => return node "Pnotl" [← (enc_Asm_ireg fuel) arg0]
    | .Pnotq arg0 => return node "Pnotq" [← (enc_Asm_ireg fuel) arg0]
    | .Psall_rcl arg0 => return node "Psall_rcl" [← (enc_Asm_ireg fuel) arg0]
    | .Psalq_rcl arg0 => return node "Psalq_rcl" [← (enc_Asm_ireg fuel) arg0]
    | .Psall_ri arg0 arg1 => return node "Psall_ri" [← (enc_Asm_ireg fuel) arg0, ← (enc_int fuel) arg1]
    | .Psalq_ri arg0 arg1 => return node "Psalq_ri" [← (enc_Asm_ireg fuel) arg0, ← (enc_int fuel) arg1]
    | .Pshrl_rcl arg0 => return node "Pshrl_rcl" [← (enc_Asm_ireg fuel) arg0]
    | .Pshrq_rcl arg0 => return node "Pshrq_rcl" [← (enc_Asm_ireg fuel) arg0]
    | .Pshrl_ri arg0 arg1 => return node "Pshrl_ri" [← (enc_Asm_ireg fuel) arg0, ← (enc_int fuel) arg1]
    | .Pshrq_ri arg0 arg1 => return node "Pshrq_ri" [← (enc_Asm_ireg fuel) arg0, ← (enc_int fuel) arg1]
    | .Psarl_rcl arg0 => return node "Psarl_rcl" [← (enc_Asm_ireg fuel) arg0]
    | .Psarq_rcl arg0 => return node "Psarq_rcl" [← (enc_Asm_ireg fuel) arg0]
    | .Psarl_ri arg0 arg1 => return node "Psarl_ri" [← (enc_Asm_ireg fuel) arg0, ← (enc_int fuel) arg1]
    | .Psarq_ri arg0 arg1 => return node "Psarq_ri" [← (enc_Asm_ireg fuel) arg0, ← (enc_int fuel) arg1]
    | .Pshld_ri arg0 arg1 arg2 => return node "Pshld_ri" [← (enc_Asm_ireg fuel) arg0, ← (enc_Asm_ireg fuel) arg1, ← (enc_int fuel) arg2]
    | .Prorl_ri arg0 arg1 => return node "Prorl_ri" [← (enc_Asm_ireg fuel) arg0, ← (enc_int fuel) arg1]
    | .Prorq_ri arg0 arg1 => return node "Prorq_ri" [← (enc_Asm_ireg fuel) arg0, ← (enc_int fuel) arg1]
    | .Pcmpl_rr arg0 arg1 => return node "Pcmpl_rr" [← (enc_Asm_ireg fuel) arg0, ← (enc_Asm_ireg fuel) arg1]
    | .Pcmpq_rr arg0 arg1 => return node "Pcmpq_rr" [← (enc_Asm_ireg fuel) arg0, ← (enc_Asm_ireg fuel) arg1]
    | .Pcmpl_ri arg0 arg1 => return node "Pcmpl_ri" [← (enc_Asm_ireg fuel) arg0, ← (enc_int fuel) arg1]
    | .Pcmpq_ri arg0 arg1 => return node "Pcmpq_ri" [← (enc_Asm_ireg fuel) arg0, ← (enc_long fuel) arg1]
    | .Ptestl_rr arg0 arg1 => return node "Ptestl_rr" [← (enc_Asm_ireg fuel) arg0, ← (enc_Asm_ireg fuel) arg1]
    | .Ptestq_rr arg0 arg1 => return node "Ptestq_rr" [← (enc_Asm_ireg fuel) arg0, ← (enc_Asm_ireg fuel) arg1]
    | .Ptestl_ri arg0 arg1 => return node "Ptestl_ri" [← (enc_Asm_ireg fuel) arg0, ← (enc_int fuel) arg1]
    | .Ptestq_ri arg0 arg1 => return node "Ptestq_ri" [← (enc_Asm_ireg fuel) arg0, ← (enc_long fuel) arg1]
    | .Pcmov arg0 arg1 arg2 => return node "Pcmov" [← (enc_Asm_testcond fuel) arg0, ← (enc_Asm_ireg fuel) arg1, ← (enc_Asm_ireg fuel) arg2]
    | .Psetcc arg0 arg1 => return node "Psetcc" [← (enc_Asm_testcond fuel) arg0, ← (enc_Asm_ireg fuel) arg1]
    | .Paddd_ff arg0 arg1 => return node "Paddd_ff" [← (enc_Asm_freg fuel) arg0, ← (enc_Asm_freg fuel) arg1]
    | .Psubd_ff arg0 arg1 => return node "Psubd_ff" [← (enc_Asm_freg fuel) arg0, ← (enc_Asm_freg fuel) arg1]
    | .Pmuld_ff arg0 arg1 => return node "Pmuld_ff" [← (enc_Asm_freg fuel) arg0, ← (enc_Asm_freg fuel) arg1]
    | .Pdivd_ff arg0 arg1 => return node "Pdivd_ff" [← (enc_Asm_freg fuel) arg0, ← (enc_Asm_freg fuel) arg1]
    | .Pnegd arg0 => return node "Pnegd" [← (enc_Asm_freg fuel) arg0]
    | .Pabsd arg0 => return node "Pabsd" [← (enc_Asm_freg fuel) arg0]
    | .Pcomisd_ff arg0 arg1 => return node "Pcomisd_ff" [← (enc_Asm_freg fuel) arg0, ← (enc_Asm_freg fuel) arg1]
    | .Pxorpd_f arg0 => return node "Pxorpd_f" [← (enc_Asm_freg fuel) arg0]
    | .Padds_ff arg0 arg1 => return node "Padds_ff" [← (enc_Asm_freg fuel) arg0, ← (enc_Asm_freg fuel) arg1]
    | .Psubs_ff arg0 arg1 => return node "Psubs_ff" [← (enc_Asm_freg fuel) arg0, ← (enc_Asm_freg fuel) arg1]
    | .Pmuls_ff arg0 arg1 => return node "Pmuls_ff" [← (enc_Asm_freg fuel) arg0, ← (enc_Asm_freg fuel) arg1]
    | .Pdivs_ff arg0 arg1 => return node "Pdivs_ff" [← (enc_Asm_freg fuel) arg0, ← (enc_Asm_freg fuel) arg1]
    | .Pnegs arg0 => return node "Pnegs" [← (enc_Asm_freg fuel) arg0]
    | .Pabss arg0 => return node "Pabss" [← (enc_Asm_freg fuel) arg0]
    | .Pcomiss_ff arg0 arg1 => return node "Pcomiss_ff" [← (enc_Asm_freg fuel) arg0, ← (enc_Asm_freg fuel) arg1]
    | .Pxorps_f arg0 => return node "Pxorps_f" [← (enc_Asm_freg fuel) arg0]
    | .Pjmp_l arg0 => return node "Pjmp_l" [← (enc_pos fuel) arg0]
    | .Pjmp_s arg0 arg1 => return node "Pjmp_s" [← (enc_pos fuel) arg0, ← (enc_AST_signature fuel) arg1]
    | .Pjmp_r arg0 arg1 => return node "Pjmp_r" [← (enc_Asm_ireg fuel) arg0, ← (enc_AST_signature fuel) arg1]
    | .Pjcc arg0 arg1 => return node "Pjcc" [← (enc_Asm_testcond fuel) arg0, ← (enc_pos fuel) arg1]
    | .Pjcc2 arg0 arg1 arg2 => return node "Pjcc2" [← (enc_Asm_testcond fuel) arg0, ← (enc_Asm_testcond fuel) arg1, ← (enc_pos fuel) arg2]
    | .Pjmptbl arg0 arg1 => return node "Pjmptbl" [← (enc_Asm_ireg fuel) arg0, ← (encList (enc_pos fuel)) arg1]
    | .Pcall_s arg0 arg1 => return node "Pcall_s" [← (enc_pos fuel) arg0, ← (enc_AST_signature fuel) arg1]
    | .Pcall_r arg0 arg1 => return node "Pcall_r" [← (enc_Asm_ireg fuel) arg0, ← (enc_AST_signature fuel) arg1]
    | .Pret => return node "Pret" []
    | .Pmov_rm_a arg0 arg1 => return node "Pmov_rm_a" [← (enc_Asm_ireg fuel) arg0, ← (enc_Asm_addrmode fuel) arg1]
    | .Pmov_mr_a arg0 arg1 => return node "Pmov_mr_a" [← (enc_Asm_addrmode fuel) arg0, ← (enc_Asm_ireg fuel) arg1]
    | .Pmovsd_fm_a arg0 arg1 => return node "Pmovsd_fm_a" [← (enc_Asm_freg fuel) arg0, ← (enc_Asm_addrmode fuel) arg1]
    | .Pmovsd_mf_a arg0 arg1 => return node "Pmovsd_mf_a" [← (enc_Asm_addrmode fuel) arg0, ← (enc_Asm_freg fuel) arg1]
    | .Plabel arg0 => return node "Plabel" [← (enc_pos fuel) arg0]
    | .Pallocframe arg0 arg1 arg2 => return node "Pallocframe" [← (enc_z fuel) arg0, ← (enc_ptr fuel) arg1, ← (enc_ptr fuel) arg2]
    | .Pfreeframe arg0 arg1 arg2 => return node "Pfreeframe" [← (enc_z fuel) arg0, ← (enc_ptr fuel) arg1, ← (enc_ptr fuel) arg2]
    | .Pbuiltin arg0 arg1 arg2 => return node "Pbuiltin" [← (enc_AST_external_function fuel) arg0, ← (encList (enc_A_builtin_arg fuel)) arg1, ← (enc_A_builtin_res fuel) arg2]
    | .Padcl_ri arg0 arg1 => return node "Padcl_ri" [← (enc_Asm_ireg fuel) arg0, ← (enc_int fuel) arg1]
    | .Padcl_rr arg0 arg1 => return node "Padcl_rr" [← (enc_Asm_ireg fuel) arg0, ← (enc_Asm_ireg fuel) arg1]
    | .Paddl_mi arg0 arg1 => return node "Paddl_mi" [← (enc_Asm_addrmode fuel) arg0, ← (enc_int fuel) arg1]
    | .Paddl_rr arg0 arg1 => return node "Paddl_rr" [← (enc_Asm_ireg fuel) arg0, ← (enc_Asm_ireg fuel) arg1]
    | .Pbsfl arg0 arg1 => return node "Pbsfl" [← (enc_Asm_ireg fuel) arg0, ← (enc_Asm_ireg fuel) arg1]
    | .Pbsfq arg0 arg1 => return node "Pbsfq" [← (enc_Asm_ireg fuel) arg0, ← (enc_Asm_ireg fuel) arg1]
    | .Pbsrl arg0 arg1 => return node "Pbsrl" [← (enc_Asm_ireg fuel) arg0, ← (enc_Asm_ireg fuel) arg1]
    | .Pbsrq arg0 arg1 => return node "Pbsrq" [← (enc_Asm_ireg fuel) arg0, ← (enc_Asm_ireg fuel) arg1]
    | .Pbswap64 arg0 => return node "Pbswap64" [← (enc_Asm_ireg fuel) arg0]
    | .Pbswap32 arg0 => return node "Pbswap32" [← (enc_Asm_ireg fuel) arg0]
    | .Pbswap16 arg0 => return node "Pbswap16" [← (enc_Asm_ireg fuel) arg0]
    | .Pcfi_adjust arg0 => return node "Pcfi_adjust" [← (enc_int fuel) arg0]
    | .Pfmadd132 arg0 arg1 arg2 => return node "Pfmadd132" [← (enc_Asm_freg fuel) arg0, ← (enc_Asm_freg fuel) arg1, ← (enc_Asm_freg fuel) arg2]
    | .Pfmadd213 arg0 arg1 arg2 => return node "Pfmadd213" [← (enc_Asm_freg fuel) arg0, ← (enc_Asm_freg fuel) arg1, ← (enc_Asm_freg fuel) arg2]
    | .Pfmadd231 arg0 arg1 arg2 => return node "Pfmadd231" [← (enc_Asm_freg fuel) arg0, ← (enc_Asm_freg fuel) arg1, ← (enc_Asm_freg fuel) arg2]
    | .Pfmsub132 arg0 arg1 arg2 => return node "Pfmsub132" [← (enc_Asm_freg fuel) arg0, ← (enc_Asm_freg fuel) arg1, ← (enc_Asm_freg fuel) arg2]
    | .Pfmsub213 arg0 arg1 arg2 => return node "Pfmsub213" [← (enc_Asm_freg fuel) arg0, ← (enc_Asm_freg fuel) arg1, ← (enc_Asm_freg fuel) arg2]
    | .Pfmsub231 arg0 arg1 arg2 => return node "Pfmsub231" [← (enc_Asm_freg fuel) arg0, ← (enc_Asm_freg fuel) arg1, ← (enc_Asm_freg fuel) arg2]
    | .Pfnmadd132 arg0 arg1 arg2 => return node "Pfnmadd132" [← (enc_Asm_freg fuel) arg0, ← (enc_Asm_freg fuel) arg1, ← (enc_Asm_freg fuel) arg2]
    | .Pfnmadd213 arg0 arg1 arg2 => return node "Pfnmadd213" [← (enc_Asm_freg fuel) arg0, ← (enc_Asm_freg fuel) arg1, ← (enc_Asm_freg fuel) arg2]
    | .Pfnmadd231 arg0 arg1 arg2 => return node "Pfnmadd231" [← (enc_Asm_freg fuel) arg0, ← (enc_Asm_freg fuel) arg1, ← (enc_Asm_freg fuel) arg2]
    | .Pfnmsub132 arg0 arg1 arg2 => return node "Pfnmsub132" [← (enc_Asm_freg fuel) arg0, ← (enc_Asm_freg fuel) arg1, ← (enc_Asm_freg fuel) arg2]
    | .Pfnmsub213 arg0 arg1 arg2 => return node "Pfnmsub213" [← (enc_Asm_freg fuel) arg0, ← (enc_Asm_freg fuel) arg1, ← (enc_Asm_freg fuel) arg2]
    | .Pfnmsub231 arg0 arg1 arg2 => return node "Pfnmsub231" [← (enc_Asm_freg fuel) arg0, ← (enc_Asm_freg fuel) arg1, ← (enc_Asm_freg fuel) arg2]
    | .Pmaxsd arg0 arg1 => return node "Pmaxsd" [← (enc_Asm_freg fuel) arg0, ← (enc_Asm_freg fuel) arg1]
    | .Pminsd arg0 arg1 => return node "Pminsd" [← (enc_Asm_freg fuel) arg0, ← (enc_Asm_freg fuel) arg1]
    | .Pmovb_rm arg0 arg1 => return node "Pmovb_rm" [← (enc_Asm_ireg fuel) arg0, ← (enc_Asm_addrmode fuel) arg1]
    | .Pmovq_rf arg0 arg1 => return node "Pmovq_rf" [← (enc_Asm_ireg fuel) arg0, ← (enc_Asm_freg fuel) arg1]
    | .Pmovsq_mr arg0 arg1 => return node "Pmovsq_mr" [← (enc_Asm_addrmode fuel) arg0, ← (enc_Asm_freg fuel) arg1]
    | .Pmovsq_rm arg0 arg1 => return node "Pmovsq_rm" [← (enc_Asm_freg fuel) arg0, ← (enc_Asm_addrmode fuel) arg1]
    | .Pmovsb => return node "Pmovsb" []
    | .Pmovsw => return node "Pmovsw" []
    | .Pmovw_rm arg0 arg1 => return node "Pmovw_rm" [← (enc_Asm_ireg fuel) arg0, ← (enc_Asm_addrmode fuel) arg1]
    | .Pnop => return node "Pnop" []
    | .Prep_movsl => return node "Prep_movsl" []
    | .Psbbl_rr arg0 arg1 => return node "Psbbl_rr" [← (enc_Asm_ireg fuel) arg0, ← (enc_Asm_ireg fuel) arg1]
    | .Psqrtsd arg0 arg1 => return node "Psqrtsd" [← (enc_Asm_freg fuel) arg0, ← (enc_Asm_freg fuel) arg1]
    | .Psubl_ri arg0 arg1 => return node "Psubl_ri" [← (enc_Asm_ireg fuel) arg0, ← (enc_int fuel) arg1]
    | .Psubq_ri arg0 arg1 => return node "Psubq_ri" [← (enc_Asm_ireg fuel) arg0, ← (enc_long fuel) arg1]

def enc_Asm_coq_function : Nat → X86.Asm.function → CodecResult Json
  | 0, _ => throw "interchange depth exceeded"
  | fuel + 1, value => do
    return node "Asm_coq_function" [← (enc_AST_signature fuel) value.fn_sig, ← (encList (enc_Asm_instruction fuel)) value.fn_code]

def enc_CFundef : Nat → Cfrontend.Ctypes.fundef (Cfrontend.Csyntax.function) → CodecResult Json
  | 0, _ => throw "interchange depth exceeded"
  | fuel + 1, value => do
    match value with
    | .Internal arg0 => return node "Internal" [← (enc_Csyntax_coq_function fuel) arg0]
    | .External arg0 arg1 arg2 arg3 => return node "External" [← (enc_AST_external_function fuel) arg0, ← (encList (enc_Ctypes_coq_type fuel)) arg1, ← (enc_Ctypes_coq_type fuel) arg2, ← (enc_AST_calling_convention fuel) arg3]

def enc_CGlobvar : Nat → Common.AST.globvar (Cfrontend.Ctypes.type) → CodecResult Json
  | 0, _ => throw "interchange depth exceeded"
  | fuel + 1, value => do
    return node "CGlobvar" [← (enc_Ctypes_coq_type fuel) value.gvar_info, ← (encList (enc_AST_init_data fuel)) value.gvar_init, ← (enc_bool fuel) value.gvar_readonly, ← (enc_bool fuel) value.gvar_volatile]

def enc_CGlobdef : Nat → Common.AST.globdef (Cfrontend.Ctypes.fundef (Cfrontend.Csyntax.function)) (Cfrontend.Ctypes.type) → CodecResult Json
  | 0, _ => throw "interchange depth exceeded"
  | fuel + 1, value => do
    match value with
    | .Gfun arg0 => return node "Gfun" [← (enc_CFundef fuel) arg0]
    | .Gvar arg0 => return node "Gvar" [← (enc_CGlobvar fuel) arg0]

def enc_AFundef : Nat → Common.AST.fundef (X86.Asm.function) → CodecResult Json
  | 0, _ => throw "interchange depth exceeded"
  | fuel + 1, value => do
    match value with
    | .Internal arg0 => return node "Internal" [← (enc_Asm_coq_function fuel) arg0]
    | .External arg0 => return node "External" [← (enc_AST_external_function fuel) arg0]

def enc_AGlobvar : Nat → Common.AST.globvar (Unit) → CodecResult Json
  | 0, _ => throw "interchange depth exceeded"
  | fuel + 1, value => do
    return node "AGlobvar" [← (enc_unit fuel) value.gvar_info, ← (encList (enc_AST_init_data fuel)) value.gvar_init, ← (enc_bool fuel) value.gvar_readonly, ← (enc_bool fuel) value.gvar_volatile]

def enc_AGlobdef : Nat → Common.AST.globdef (Common.AST.fundef (X86.Asm.function)) (Unit) → CodecResult Json
  | 0, _ => throw "interchange depth exceeded"
  | fuel + 1, value => do
    match value with
    | .Gfun arg0 => return node "Gfun" [← (enc_AFundef fuel) arg0]
    | .Gvar arg0 => return node "Gvar" [← (enc_AGlobvar fuel) arg0]

def enc_AProgram : Nat → X86.Asm.program → CodecResult Json
  | 0, _ => throw "interchange depth exceeded"
  | fuel + 1, value => do
    return node "AProgram" [← (encList (encPair (enc_pos fuel) (enc_AGlobdef fuel))) value.prog_defs, ← (encList (enc_pos fuel)) value.prog_public, ← (enc_pos fuel) value.prog_main]

def enc_A_builtin_arg : Nat → Common.AST.builtin_arg X86.Asm.preg → CodecResult Json
  | 0, _ => throw "interchange depth exceeded"
  | fuel + 1, value => do
    match value with
    | .BA arg0 => return node "BA" [← (enc_Asm_preg fuel) arg0]
    | .BA_int arg0 => return node "BA_int" [← (enc_int fuel) arg0]
    | .BA_long arg0 => return node "BA_long" [← (enc_long fuel) arg0]
    | .BA_float arg0 => return node "BA_float" [← (enc_float fuel) arg0]
    | .BA_single arg0 => return node "BA_single" [← (enc_single fuel) arg0]
    | .BA_loadstack arg0 arg1 => return node "BA_loadstack" [← (enc_AST_memory_chunk fuel) arg0, ← (enc_ptr fuel) arg1]
    | .BA_addrstack arg0 => return node "BA_addrstack" [← (enc_ptr fuel) arg0]
    | .BA_loadglobal arg0 arg1 arg2 => return node "BA_loadglobal" [← (enc_AST_memory_chunk fuel) arg0, ← (enc_pos fuel) arg1, ← (enc_ptr fuel) arg2]
    | .BA_addrglobal arg0 arg1 => return node "BA_addrglobal" [← (enc_pos fuel) arg0, ← (enc_ptr fuel) arg1]
    | .BA_splitlong arg0 arg1 => return node "BA_splitlong" [← (enc_A_builtin_arg fuel) arg0, ← (enc_A_builtin_arg fuel) arg1]
    | .BA_addptr arg0 arg1 => return node "BA_addptr" [← (enc_A_builtin_arg fuel) arg0, ← (enc_A_builtin_arg fuel) arg1]

def enc_A_builtin_res : Nat → Common.AST.builtin_res X86.Asm.preg → CodecResult Json
  | 0, _ => throw "interchange depth exceeded"
  | fuel + 1, value => do
    match value with
    | .BR arg0 => return node "BR" [← (enc_Asm_preg fuel) arg0]
    | .BR_none => return node "BR_none" []
    | .BR_splitlong arg0 arg1 => return node "BR_splitlong" [← (enc_A_builtin_res fuel) arg0, ← (enc_A_builtin_res fuel) arg1]

end

mutual
def dec_AST_typ : Nat → Json → CodecResult (Common.AST.typ)
  | 0, _ => throw "interchange depth exceeded"
  | fuel + 1, value => do
    let values ← value.getArr?
    if size : values.size = 1 then
      match values[0] with
      | .str "Tint" =>
        return .Tint
      | .str "Tfloat" =>
        return .Tfloat
      | .str "Tlong" =>
        return .Tlong
      | .str "Tsingle" =>
        return .Tsingle
      | .str "Tany32" =>
        return .Tany32
      | .str "Tany64" =>
        return .Tany64
      | _ => throw "invalid AST_typ constructor or arity"
    else throw "invalid AST_typ constructor or arity"

def dec_AST_xtype : Nat → Json → CodecResult (Common.AST.xtype)
  | 0, _ => throw "interchange depth exceeded"
  | fuel + 1, value => do
    let values ← value.getArr?
    if size : values.size = 1 then
      match values[0] with
      | .str "Xbool" =>
        return .Xbool
      | .str "Xint8signed" =>
        return .Xint8signed
      | .str "Xint8unsigned" =>
        return .Xint8unsigned
      | .str "Xint16signed" =>
        return .Xint16signed
      | .str "Xint16unsigned" =>
        return .Xint16unsigned
      | .str "Xint" =>
        return .Xint
      | .str "Xfloat" =>
        return .Xfloat
      | .str "Xlong" =>
        return .Xlong
      | .str "Xsingle" =>
        return .Xsingle
      | .str "Xptr" =>
        return .Xptr
      | .str "Xany32" =>
        return .Xany32
      | .str "Xany64" =>
        return .Xany64
      | .str "Xvoid" =>
        return .Xvoid
      | _ => throw "invalid AST_xtype constructor or arity"
    else throw "invalid AST_xtype constructor or arity"

def dec_AST_calling_convention : Nat → Json → CodecResult (Common.AST.calling_convention)
  | 0, _ => throw "interchange depth exceeded"
  | fuel + 1, value => do
    let values ← value.getArr?
    if size : values.size = 4 then
      match values[0] with
      | .str "AST_calling_convention" =>
        return { cc_vararg := (← (decOption (dec_z fuel)) values[1]), cc_unproto := (← (dec_bool fuel) values[2]), cc_structret := (← (dec_bool fuel) values[3]) }
      | _ => throw "invalid AST_calling_convention constructor or arity"
    else throw "invalid AST_calling_convention constructor or arity"

def dec_AST_signature : Nat → Json → CodecResult (Common.AST.signature)
  | 0, _ => throw "interchange depth exceeded"
  | fuel + 1, value => do
    let values ← value.getArr?
    if size : values.size = 4 then
      match values[0] with
      | .str "AST_signature" =>
        return { sig_args := (← (decList (dec_AST_xtype fuel)) values[1]), sig_res := (← (dec_AST_xtype fuel) values[2]), sig_cc := (← (dec_AST_calling_convention fuel) values[3]) }
      | _ => throw "invalid AST_signature constructor or arity"
    else throw "invalid AST_signature constructor or arity"

def dec_AST_memory_chunk : Nat → Json → CodecResult (Common.AST.memory_chunk)
  | 0, _ => throw "interchange depth exceeded"
  | fuel + 1, value => do
    let values ← value.getArr?
    if size : values.size = 1 then
      match values[0] with
      | .str "Mbool" =>
        return .Mbool
      | .str "Mint8signed" =>
        return .Mint8signed
      | .str "Mint8unsigned" =>
        return .Mint8unsigned
      | .str "Mint16signed" =>
        return .Mint16signed
      | .str "Mint16unsigned" =>
        return .Mint16unsigned
      | .str "Mint32" =>
        return .Mint32
      | .str "Mint64" =>
        return .Mint64
      | .str "Mfloat32" =>
        return .Mfloat32
      | .str "Mfloat64" =>
        return .Mfloat64
      | .str "Many32" =>
        return .Many32
      | .str "Many64" =>
        return .Many64
      | _ => throw "invalid AST_memory_chunk constructor or arity"
    else throw "invalid AST_memory_chunk constructor or arity"

def dec_AST_init_data : Nat → Json → CodecResult (Common.AST.init_data)
  | 0, _ => throw "interchange depth exceeded"
  | fuel + 1, value => do
    let values ← value.getArr?
    if size : values.size = 2 then
      match values[0] with
      | .str "Init_int8" =>
        return .Init_int8 (← (dec_int fuel) values[1])
      | .str "Init_int16" =>
        return .Init_int16 (← (dec_int fuel) values[1])
      | .str "Init_int32" =>
        return .Init_int32 (← (dec_int fuel) values[1])
      | .str "Init_int64" =>
        return .Init_int64 (← (dec_long fuel) values[1])
      | .str "Init_float32" =>
        return .Init_float32 (← (dec_single fuel) values[1])
      | .str "Init_float64" =>
        return .Init_float64 (← (dec_float fuel) values[1])
      | .str "Init_space" =>
        return .Init_space (← (dec_z fuel) values[1])
      | _ => throw "invalid AST_init_data constructor or arity"
    else if size : values.size = 3 then
      match values[0] with
      | .str "Init_addrof" =>
        return .Init_addrof (← (dec_pos fuel) values[1]) (← (dec_ptr fuel) values[2])
      | _ => throw "invalid AST_init_data constructor or arity"
    else throw "invalid AST_init_data constructor or arity"

def dec_AST_external_function : Nat → Json → CodecResult (Common.AST.external_function)
  | 0, _ => throw "interchange depth exceeded"
  | fuel + 1, value => do
    let values ← value.getArr?
    if size : values.size = 1 then
      match values[0] with
      | .str "EF_malloc" =>
        return .EF_malloc
      | .str "EF_free" =>
        return .EF_free
      | _ => throw "invalid AST_external_function constructor or arity"
    else if size : values.size = 2 then
      match values[0] with
      | .str "EF_vload" =>
        return .EF_vload (← (dec_AST_memory_chunk fuel) values[1])
      | .str "EF_vstore" =>
        return .EF_vstore (← (dec_AST_memory_chunk fuel) values[1])
      | _ => throw "invalid AST_external_function constructor or arity"
    else if size : values.size = 3 then
      match values[0] with
      | .str "EF_external" =>
        return .EF_external (← (dec_string fuel) values[1]) (← (dec_AST_signature fuel) values[2])
      | .str "EF_builtin" =>
        return .EF_builtin (← (dec_string fuel) values[1]) (← (dec_AST_signature fuel) values[2])
      | .str "EF_runtime" =>
        return .EF_runtime (← (dec_string fuel) values[1]) (← (dec_AST_signature fuel) values[2])
      | .str "EF_memcpy" =>
        return .EF_memcpy (← (dec_z fuel) values[1]) (← (dec_z fuel) values[2])
      | _ => throw "invalid AST_external_function constructor or arity"
    else if size : values.size = 4 then
      match values[0] with
      | .str "EF_annot" =>
        return .EF_annot (← (dec_pos fuel) values[1]) (← (dec_string fuel) values[2]) (← (decList (dec_AST_typ fuel)) values[3])
      | .str "EF_annot_val" =>
        return .EF_annot_val (← (dec_pos fuel) values[1]) (← (dec_string fuel) values[2]) (← (dec_AST_typ fuel) values[3])
      | .str "EF_inline_asm" =>
        return .EF_inline_asm (← (dec_string fuel) values[1]) (← (dec_AST_signature fuel) values[2]) (← (decList (dec_string fuel)) values[3])
      | .str "EF_debug" =>
        return .EF_debug (← (dec_pos fuel) values[1]) (← (dec_pos fuel) values[2]) (← (decList (dec_AST_typ fuel)) values[3])
      | _ => throw "invalid AST_external_function constructor or arity"
    else throw "invalid AST_external_function constructor or arity"

def dec_Ctypes_signedness : Nat → Json → CodecResult (Cfrontend.Ctypes.signedness)
  | 0, _ => throw "interchange depth exceeded"
  | fuel + 1, value => do
    let values ← value.getArr?
    if size : values.size = 1 then
      match values[0] with
      | .str "Signed" =>
        return .Signed
      | .str "Unsigned" =>
        return .Unsigned
      | _ => throw "invalid Ctypes_signedness constructor or arity"
    else throw "invalid Ctypes_signedness constructor or arity"

def dec_Ctypes_intsize : Nat → Json → CodecResult (Cfrontend.Ctypes.intsize)
  | 0, _ => throw "interchange depth exceeded"
  | fuel + 1, value => do
    let values ← value.getArr?
    if size : values.size = 1 then
      match values[0] with
      | .str "I8" =>
        return .I8
      | .str "I16" =>
        return .I16
      | .str "I32" =>
        return .I32
      | .str "IBool" =>
        return .IBool
      | _ => throw "invalid Ctypes_intsize constructor or arity"
    else throw "invalid Ctypes_intsize constructor or arity"

def dec_Ctypes_floatsize : Nat → Json → CodecResult (Cfrontend.Ctypes.floatsize)
  | 0, _ => throw "interchange depth exceeded"
  | fuel + 1, value => do
    let values ← value.getArr?
    if size : values.size = 1 then
      match values[0] with
      | .str "F32" =>
        return .F32
      | .str "F64" =>
        return .F64
      | _ => throw "invalid Ctypes_floatsize constructor or arity"
    else throw "invalid Ctypes_floatsize constructor or arity"

def dec_Ctypes_attr : Nat → Json → CodecResult (Cfrontend.Ctypes.attr)
  | 0, _ => throw "interchange depth exceeded"
  | fuel + 1, value => do
    let values ← value.getArr?
    if size : values.size = 3 then
      match values[0] with
      | .str "Ctypes_attr" =>
        return { attr_volatile := (← (dec_bool fuel) values[1]), attr_alignas := (← (decOption (dec_n fuel)) values[2]) }
      | _ => throw "invalid Ctypes_attr constructor or arity"
    else throw "invalid Ctypes_attr constructor or arity"

def dec_Ctypes_coq_type : Nat → Json → CodecResult (Cfrontend.Ctypes.type)
  | 0, _ => throw "interchange depth exceeded"
  | fuel + 1, value => do
    let values ← value.getArr?
    if size : values.size = 1 then
      match values[0] with
      | .str "Tvoid" =>
        return .Tvoid
      | _ => throw "invalid Ctypes_coq_type constructor or arity"
    else if size : values.size = 3 then
      match values[0] with
      | .str "Tlong" =>
        return .Tlong (← (dec_Ctypes_signedness fuel) values[1]) (← (dec_Ctypes_attr fuel) values[2])
      | .str "Tfloat" =>
        return .Tfloat (← (dec_Ctypes_floatsize fuel) values[1]) (← (dec_Ctypes_attr fuel) values[2])
      | .str "Tpointer" =>
        return .Tpointer (← (dec_Ctypes_coq_type fuel) values[1]) (← (dec_Ctypes_attr fuel) values[2])
      | .str "Tstruct" =>
        return .Tstruct (← (dec_pos fuel) values[1]) (← (dec_Ctypes_attr fuel) values[2])
      | .str "Tunion" =>
        return .Tunion (← (dec_pos fuel) values[1]) (← (dec_Ctypes_attr fuel) values[2])
      | _ => throw "invalid Ctypes_coq_type constructor or arity"
    else if size : values.size = 4 then
      match values[0] with
      | .str "Tint" =>
        return .Tint (← (dec_Ctypes_intsize fuel) values[1]) (← (dec_Ctypes_signedness fuel) values[2]) (← (dec_Ctypes_attr fuel) values[3])
      | .str "Tarray" =>
        return .Tarray (← (dec_Ctypes_coq_type fuel) values[1]) (← (dec_z fuel) values[2]) (← (dec_Ctypes_attr fuel) values[3])
      | .str "Tfunction" =>
        return .Tfunction (← (decList (dec_Ctypes_coq_type fuel)) values[1]) (← (dec_Ctypes_coq_type fuel) values[2]) (← (dec_AST_calling_convention fuel) values[3])
      | _ => throw "invalid Ctypes_coq_type constructor or arity"
    else throw "invalid Ctypes_coq_type constructor or arity"

def dec_Ctypes_struct_or_union : Nat → Json → CodecResult (Cfrontend.Ctypes.struct_or_union)
  | 0, _ => throw "interchange depth exceeded"
  | fuel + 1, value => do
    let values ← value.getArr?
    if size : values.size = 1 then
      match values[0] with
      | .str "Struct" =>
        return .Struct
      | .str "Union" =>
        return .Union
      | _ => throw "invalid Ctypes_struct_or_union constructor or arity"
    else throw "invalid Ctypes_struct_or_union constructor or arity"

def dec_Ctypes_member : Nat → Json → CodecResult (Cfrontend.Ctypes.member)
  | 0, _ => throw "interchange depth exceeded"
  | fuel + 1, value => do
    let values ← value.getArr?
    if size : values.size = 3 then
      match values[0] with
      | .str "Member_plain" =>
        return .Member_plain (← (dec_pos fuel) values[1]) (← (dec_Ctypes_coq_type fuel) values[2])
      | _ => throw "invalid Ctypes_member constructor or arity"
    else if size : values.size = 7 then
      match values[0] with
      | .str "Member_bitfield" =>
        return .Member_bitfield (← (dec_pos fuel) values[1]) (← (dec_Ctypes_intsize fuel) values[2]) (← (dec_Ctypes_signedness fuel) values[3]) (← (dec_Ctypes_attr fuel) values[4]) (← (dec_z fuel) values[5]) (← (dec_bool fuel) values[6])
      | _ => throw "invalid Ctypes_member constructor or arity"
    else throw "invalid Ctypes_member constructor or arity"

def dec_Ctypes_composite_definition : Nat → Json → CodecResult (Cfrontend.Ctypes.composite_definition)
  | 0, _ => throw "interchange depth exceeded"
  | fuel + 1, value => do
    let values ← value.getArr?
    if size : values.size = 5 then
      match values[0] with
      | .str "Composite" =>
        return .Composite (← (dec_pos fuel) values[1]) (← (dec_Ctypes_struct_or_union fuel) values[2]) (← (decList (dec_Ctypes_member fuel)) values[3]) (← (dec_Ctypes_attr fuel) values[4])
      | _ => throw "invalid Ctypes_composite_definition constructor or arity"
    else throw "invalid Ctypes_composite_definition constructor or arity"

def dec_Ctypes_bitfield : Nat → Json → CodecResult (Cfrontend.Ctypes.bitfield)
  | 0, _ => throw "interchange depth exceeded"
  | fuel + 1, value => do
    let values ← value.getArr?
    if size : values.size = 1 then
      match values[0] with
      | .str "Full" =>
        return .Full
      | _ => throw "invalid Ctypes_bitfield constructor or arity"
    else if size : values.size = 5 then
      match values[0] with
      | .str "Bits" =>
        return .Bits (← (dec_Ctypes_intsize fuel) values[1]) (← (dec_Ctypes_signedness fuel) values[2]) (← (dec_z fuel) values[3]) (← (dec_z fuel) values[4])
      | _ => throw "invalid Ctypes_bitfield constructor or arity"
    else throw "invalid Ctypes_bitfield constructor or arity"

def dec_Cop_unary_operation : Nat → Json → CodecResult (Cfrontend.Cop.unary_operation)
  | 0, _ => throw "interchange depth exceeded"
  | fuel + 1, value => do
    let values ← value.getArr?
    if size : values.size = 1 then
      match values[0] with
      | .str "Onotbool" =>
        return .Onotbool
      | .str "Onotint" =>
        return .Onotint
      | .str "Oneg" =>
        return .Oneg
      | .str "Oabsfloat" =>
        return .Oabsfloat
      | _ => throw "invalid Cop_unary_operation constructor or arity"
    else throw "invalid Cop_unary_operation constructor or arity"

def dec_Cop_binary_operation : Nat → Json → CodecResult (Cfrontend.Cop.binary_operation)
  | 0, _ => throw "interchange depth exceeded"
  | fuel + 1, value => do
    let values ← value.getArr?
    if size : values.size = 1 then
      match values[0] with
      | .str "Oadd" =>
        return .Oadd
      | .str "Osub" =>
        return .Osub
      | .str "Omul" =>
        return .Omul
      | .str "Odiv" =>
        return .Odiv
      | .str "Omod" =>
        return .Omod
      | .str "Oand" =>
        return .Oand
      | .str "Oor" =>
        return .Oor
      | .str "Oxor" =>
        return .Oxor
      | .str "Oshl" =>
        return .Oshl
      | .str "Oshr" =>
        return .Oshr
      | .str "Oeq" =>
        return .Oeq
      | .str "One" =>
        return .One
      | .str "Olt" =>
        return .Olt
      | .str "Ogt" =>
        return .Ogt
      | .str "Ole" =>
        return .Ole
      | .str "Oge" =>
        return .Oge
      | _ => throw "invalid Cop_binary_operation constructor or arity"
    else throw "invalid Cop_binary_operation constructor or arity"

def dec_Cop_incr_or_decr : Nat → Json → CodecResult (Cfrontend.Cop.incr_or_decr)
  | 0, _ => throw "interchange depth exceeded"
  | fuel + 1, value => do
    let values ← value.getArr?
    if size : values.size = 1 then
      match values[0] with
      | .str "Incr" =>
        return .Incr
      | .str "Decr" =>
        return .Decr
      | _ => throw "invalid Cop_incr_or_decr constructor or arity"
    else throw "invalid Cop_incr_or_decr constructor or arity"

def dec_Values_coq_val : Nat → Json → CodecResult (Common.Values.val)
  | 0, _ => throw "interchange depth exceeded"
  | fuel + 1, value => do
    let values ← value.getArr?
    if size : values.size = 1 then
      match values[0] with
      | .str "Vundef" =>
        return .Vundef
      | _ => throw "invalid Values_coq_val constructor or arity"
    else if size : values.size = 2 then
      match values[0] with
      | .str "Vint" =>
        return .Vint (← (dec_int fuel) values[1])
      | .str "Vlong" =>
        return .Vlong (← (dec_long fuel) values[1])
      | .str "Vfloat" =>
        return .Vfloat (← (dec_float fuel) values[1])
      | .str "Vsingle" =>
        return .Vsingle (← (dec_single fuel) values[1])
      | _ => throw "invalid Values_coq_val constructor or arity"
    else if size : values.size = 3 then
      match values[0] with
      | .str "Vptr" =>
        return .Vptr (← (dec_pos fuel) values[1]) (← (dec_ptr fuel) values[2])
      | _ => throw "invalid Values_coq_val constructor or arity"
    else throw "invalid Values_coq_val constructor or arity"

def dec_Csyntax_expr : Nat → Json → CodecResult (Cfrontend.Csyntax.expr)
  | 0, _ => throw "interchange depth exceeded"
  | fuel + 1, value => do
    let values ← value.getArr?
    if size : values.size = 3 then
      match values[0] with
      | .str "Eval" =>
        return .Eval (← (dec_Values_coq_val fuel) values[1]) (← (dec_Ctypes_coq_type fuel) values[2])
      | .str "Evar" =>
        return .Evar (← (dec_pos fuel) values[1]) (← (dec_Ctypes_coq_type fuel) values[2])
      | .str "Evalof" =>
        return .Evalof (← (dec_Csyntax_expr fuel) values[1]) (← (dec_Ctypes_coq_type fuel) values[2])
      | .str "Ederef" =>
        return .Ederef (← (dec_Csyntax_expr fuel) values[1]) (← (dec_Ctypes_coq_type fuel) values[2])
      | .str "Eaddrof" =>
        return .Eaddrof (← (dec_Csyntax_expr fuel) values[1]) (← (dec_Ctypes_coq_type fuel) values[2])
      | .str "Ecast" =>
        return .Ecast (← (dec_Csyntax_expr fuel) values[1]) (← (dec_Ctypes_coq_type fuel) values[2])
      | .str "Esizeof" =>
        return .Esizeof (← (dec_Ctypes_coq_type fuel) values[1]) (← (dec_Ctypes_coq_type fuel) values[2])
      | .str "Ealignof" =>
        return .Ealignof (← (dec_Ctypes_coq_type fuel) values[1]) (← (dec_Ctypes_coq_type fuel) values[2])
      | _ => throw "invalid Csyntax_expr constructor or arity"
    else if size : values.size = 4 then
      match values[0] with
      | .str "Efield" =>
        return .Efield (← (dec_Csyntax_expr fuel) values[1]) (← (dec_pos fuel) values[2]) (← (dec_Ctypes_coq_type fuel) values[3])
      | .str "Eunop" =>
        return .Eunop (← (dec_Cop_unary_operation fuel) values[1]) (← (dec_Csyntax_expr fuel) values[2]) (← (dec_Ctypes_coq_type fuel) values[3])
      | .str "Eseqand" =>
        return .Eseqand (← (dec_Csyntax_expr fuel) values[1]) (← (dec_Csyntax_expr fuel) values[2]) (← (dec_Ctypes_coq_type fuel) values[3])
      | .str "Eseqor" =>
        return .Eseqor (← (dec_Csyntax_expr fuel) values[1]) (← (dec_Csyntax_expr fuel) values[2]) (← (dec_Ctypes_coq_type fuel) values[3])
      | .str "Eassign" =>
        return .Eassign (← (dec_Csyntax_expr fuel) values[1]) (← (dec_Csyntax_expr fuel) values[2]) (← (dec_Ctypes_coq_type fuel) values[3])
      | .str "Epostincr" =>
        return .Epostincr (← (dec_Cop_incr_or_decr fuel) values[1]) (← (dec_Csyntax_expr fuel) values[2]) (← (dec_Ctypes_coq_type fuel) values[3])
      | .str "Ecomma" =>
        return .Ecomma (← (dec_Csyntax_expr fuel) values[1]) (← (dec_Csyntax_expr fuel) values[2]) (← (dec_Ctypes_coq_type fuel) values[3])
      | .str "Ecall" =>
        return .Ecall (← (dec_Csyntax_expr fuel) values[1]) (← (dec_Csyntax_exprlist fuel) values[2]) (← (dec_Ctypes_coq_type fuel) values[3])
      | .str "Eparen" =>
        return .Eparen (← (dec_Csyntax_expr fuel) values[1]) (← (dec_Ctypes_coq_type fuel) values[2]) (← (dec_Ctypes_coq_type fuel) values[3])
      | _ => throw "invalid Csyntax_expr constructor or arity"
    else if size : values.size = 5 then
      match values[0] with
      | .str "Ebinop" =>
        return .Ebinop (← (dec_Cop_binary_operation fuel) values[1]) (← (dec_Csyntax_expr fuel) values[2]) (← (dec_Csyntax_expr fuel) values[3]) (← (dec_Ctypes_coq_type fuel) values[4])
      | .str "Econdition" =>
        return .Econdition (← (dec_Csyntax_expr fuel) values[1]) (← (dec_Csyntax_expr fuel) values[2]) (← (dec_Csyntax_expr fuel) values[3]) (← (dec_Ctypes_coq_type fuel) values[4])
      | .str "Ebuiltin" =>
        return .Ebuiltin (← (dec_AST_external_function fuel) values[1]) (← (decList (dec_Ctypes_coq_type fuel)) values[2]) (← (dec_Csyntax_exprlist fuel) values[3]) (← (dec_Ctypes_coq_type fuel) values[4])
      | .str "Eloc" =>
        return .Eloc (← (dec_pos fuel) values[1]) (← (dec_ptr fuel) values[2]) (← (dec_Ctypes_bitfield fuel) values[3]) (← (dec_Ctypes_coq_type fuel) values[4])
      | _ => throw "invalid Csyntax_expr constructor or arity"
    else if size : values.size = 6 then
      match values[0] with
      | .str "Eassignop" =>
        return .Eassignop (← (dec_Cop_binary_operation fuel) values[1]) (← (dec_Csyntax_expr fuel) values[2]) (← (dec_Csyntax_expr fuel) values[3]) (← (dec_Ctypes_coq_type fuel) values[4]) (← (dec_Ctypes_coq_type fuel) values[5])
      | _ => throw "invalid Csyntax_expr constructor or arity"
    else throw "invalid Csyntax_expr constructor or arity"

def dec_Csyntax_exprlist : Nat → Json → CodecResult (Cfrontend.Csyntax.exprlist)
  | 0, _ => throw "interchange depth exceeded"
  | fuel + 1, value => do
    let values ← value.getArr?
    if size : values.size = 1 then
      match values[0] with
      | .str "Enil" =>
        return .Enil
      | _ => throw "invalid Csyntax_exprlist constructor or arity"
    else if size : values.size = 3 then
      match values[0] with
      | .str "Econs" =>
        return .Econs (← (dec_Csyntax_expr fuel) values[1]) (← (dec_Csyntax_exprlist fuel) values[2])
      | _ => throw "invalid Csyntax_exprlist constructor or arity"
    else throw "invalid Csyntax_exprlist constructor or arity"

def dec_Csyntax_statement : Nat → Json → CodecResult (Cfrontend.Csyntax.statement)
  | 0, _ => throw "interchange depth exceeded"
  | fuel + 1, value => do
    let values ← value.getArr?
    if size : values.size = 1 then
      match values[0] with
      | .str "Sskip" =>
        return .Sskip
      | .str "Sbreak" =>
        return .Sbreak
      | .str "Scontinue" =>
        return .Scontinue
      | _ => throw "invalid Csyntax_statement constructor or arity"
    else if size : values.size = 2 then
      match values[0] with
      | .str "Sdo" =>
        return .Sdo (← (dec_Csyntax_expr fuel) values[1])
      | .str "Sreturn" =>
        return .Sreturn (← (decOption (dec_Csyntax_expr fuel)) values[1])
      | .str "Sgoto" =>
        return .Sgoto (← (dec_pos fuel) values[1])
      | _ => throw "invalid Csyntax_statement constructor or arity"
    else if size : values.size = 3 then
      match values[0] with
      | .str "Ssequence" =>
        return .Ssequence (← (dec_Csyntax_statement fuel) values[1]) (← (dec_Csyntax_statement fuel) values[2])
      | .str "Swhile" =>
        return .Swhile (← (dec_Csyntax_expr fuel) values[1]) (← (dec_Csyntax_statement fuel) values[2])
      | .str "Sdowhile" =>
        return .Sdowhile (← (dec_Csyntax_expr fuel) values[1]) (← (dec_Csyntax_statement fuel) values[2])
      | .str "Sswitch" =>
        return .Sswitch (← (dec_Csyntax_expr fuel) values[1]) (← (dec_Csyntax_labeled_statements fuel) values[2])
      | .str "Slabel" =>
        return .Slabel (← (dec_pos fuel) values[1]) (← (dec_Csyntax_statement fuel) values[2])
      | _ => throw "invalid Csyntax_statement constructor or arity"
    else if size : values.size = 4 then
      match values[0] with
      | .str "Sifthenelse" =>
        return .Sifthenelse (← (dec_Csyntax_expr fuel) values[1]) (← (dec_Csyntax_statement fuel) values[2]) (← (dec_Csyntax_statement fuel) values[3])
      | _ => throw "invalid Csyntax_statement constructor or arity"
    else if size : values.size = 5 then
      match values[0] with
      | .str "Sfor" =>
        return .Sfor (← (dec_Csyntax_statement fuel) values[1]) (← (dec_Csyntax_expr fuel) values[2]) (← (dec_Csyntax_statement fuel) values[3]) (← (dec_Csyntax_statement fuel) values[4])
      | _ => throw "invalid Csyntax_statement constructor or arity"
    else throw "invalid Csyntax_statement constructor or arity"

def dec_Csyntax_labeled_statements : Nat → Json → CodecResult (Cfrontend.Csyntax.labeled_statements)
  | 0, _ => throw "interchange depth exceeded"
  | fuel + 1, value => do
    let values ← value.getArr?
    if size : values.size = 1 then
      match values[0] with
      | .str "LSnil" =>
        return .LSnil
      | _ => throw "invalid Csyntax_labeled_statements constructor or arity"
    else if size : values.size = 4 then
      match values[0] with
      | .str "LScons" =>
        return .LScons (← (decOption (dec_z fuel)) values[1]) (← (dec_Csyntax_statement fuel) values[2]) (← (dec_Csyntax_labeled_statements fuel) values[3])
      | _ => throw "invalid Csyntax_labeled_statements constructor or arity"
    else throw "invalid Csyntax_labeled_statements constructor or arity"

def dec_Csyntax_coq_function : Nat → Json → CodecResult (Cfrontend.Csyntax.function)
  | 0, _ => throw "interchange depth exceeded"
  | fuel + 1, value => do
    let values ← value.getArr?
    if size : values.size = 6 then
      match values[0] with
      | .str "Csyntax_coq_function" =>
        return { fn_return := (← (dec_Ctypes_coq_type fuel) values[1]), fn_callconv := (← (dec_AST_calling_convention fuel) values[2]), fn_params := (← (decList (decPair (dec_pos fuel) (dec_Ctypes_coq_type fuel))) values[3]), fn_vars := (← (decList (decPair (dec_pos fuel) (dec_Ctypes_coq_type fuel))) values[4]), fn_body := (← (dec_Csyntax_statement fuel) values[5]) }
      | _ => throw "invalid Csyntax_coq_function constructor or arity"
    else throw "invalid Csyntax_coq_function constructor or arity"

def dec_Asm_ireg : Nat → Json → CodecResult (X86.Asm.ireg)
  | 0, _ => throw "interchange depth exceeded"
  | fuel + 1, value => do
    match ← fields value with
    | [.str "RAX"] =>
      return .RAX
    | [.str "RBX"] =>
      return .RBX
    | [.str "RCX"] =>
      return .RCX
    | [.str "RDX"] =>
      return .RDX
    | [.str "RSI"] =>
      return .RSI
    | [.str "RDI"] =>
      return .RDI
    | [.str "RBP"] =>
      return .RBP
    | [.str "RSP"] =>
      return .RSP
    | [.str "R8"] =>
      return .R8
    | [.str "R9"] =>
      return .R9
    | [.str "R10"] =>
      return .R10
    | [.str "R11"] =>
      return .R11
    | [.str "R12"] =>
      return .R12
    | [.str "R13"] =>
      return .R13
    | [.str "R14"] =>
      return .R14
    | [.str "R15"] =>
      return .R15
    | _ => throw "invalid Asm_ireg constructor or arity"

def dec_Asm_freg : Nat → Json → CodecResult (X86.Asm.freg)
  | 0, _ => throw "interchange depth exceeded"
  | fuel + 1, value => do
    match ← fields value with
    | [.str "XMM0"] =>
      return .XMM0
    | [.str "XMM1"] =>
      return .XMM1
    | [.str "XMM2"] =>
      return .XMM2
    | [.str "XMM3"] =>
      return .XMM3
    | [.str "XMM4"] =>
      return .XMM4
    | [.str "XMM5"] =>
      return .XMM5
    | [.str "XMM6"] =>
      return .XMM6
    | [.str "XMM7"] =>
      return .XMM7
    | [.str "XMM8"] =>
      return .XMM8
    | [.str "XMM9"] =>
      return .XMM9
    | [.str "XMM10"] =>
      return .XMM10
    | [.str "XMM11"] =>
      return .XMM11
    | [.str "XMM12"] =>
      return .XMM12
    | [.str "XMM13"] =>
      return .XMM13
    | [.str "XMM14"] =>
      return .XMM14
    | [.str "XMM15"] =>
      return .XMM15
    | _ => throw "invalid Asm_freg constructor or arity"

def dec_Asm_crbit : Nat → Json → CodecResult (X86.Asm.crbit)
  | 0, _ => throw "interchange depth exceeded"
  | fuel + 1, value => do
    match ← fields value with
    | [.str "ZF"] =>
      return .ZF
    | [.str "CF"] =>
      return .CF
    | [.str "PF"] =>
      return .PF
    | [.str "SF"] =>
      return .SF
    | [.str "OF"] =>
      return .OF
    | _ => throw "invalid Asm_crbit constructor or arity"

def dec_Asm_preg : Nat → Json → CodecResult (X86.Asm.preg)
  | 0, _ => throw "interchange depth exceeded"
  | fuel + 1, value => do
    match ← fields value with
    | [.str "PC"] =>
      return .PC
    | [.str "IR", arg0] =>
      return .IR (← (dec_Asm_ireg fuel) arg0)
    | [.str "FR", arg0] =>
      return .FR (← (dec_Asm_freg fuel) arg0)
    | [.str "ST0"] =>
      return .ST0
    | [.str "CR", arg0] =>
      return .CR (← (dec_Asm_crbit fuel) arg0)
    | [.str "RA"] =>
      return .RA
    | _ => throw "invalid Asm_preg constructor or arity"

def dec_Asm_addrmode : Nat → Json → CodecResult (X86.Asm.addrmode)
  | 0, _ => throw "interchange depth exceeded"
  | fuel + 1, value => do
    match ← fields value with
    | [.str "Addrmode", arg0, arg1, arg2] =>
      return .Addrmode (← (decOption (dec_Asm_ireg fuel)) arg0) (← (decOption (decPair (dec_Asm_ireg fuel) (dec_z fuel))) arg1) (← (decSum (dec_z fuel) (decPair (dec_pos fuel) (dec_ptr fuel))) arg2)
    | _ => throw "invalid Asm_addrmode constructor or arity"

def dec_Asm_testcond : Nat → Json → CodecResult (X86.Asm.testcond)
  | 0, _ => throw "interchange depth exceeded"
  | fuel + 1, value => do
    match ← fields value with
    | [.str "Cond_e"] =>
      return .Cond_e
    | [.str "Cond_ne"] =>
      return .Cond_ne
    | [.str "Cond_b"] =>
      return .Cond_b
    | [.str "Cond_be"] =>
      return .Cond_be
    | [.str "Cond_ae"] =>
      return .Cond_ae
    | [.str "Cond_a"] =>
      return .Cond_a
    | [.str "Cond_l"] =>
      return .Cond_l
    | [.str "Cond_le"] =>
      return .Cond_le
    | [.str "Cond_ge"] =>
      return .Cond_ge
    | [.str "Cond_g"] =>
      return .Cond_g
    | [.str "Cond_p"] =>
      return .Cond_p
    | [.str "Cond_np"] =>
      return .Cond_np
    | _ => throw "invalid Asm_testcond constructor or arity"

def dec_Asm_instruction : Nat → Json → CodecResult (X86.Asm.instruction)
  | 0, _ => throw "interchange depth exceeded"
  | fuel + 1, value => do
    match ← fields value with
    | [.str "Pmov_rr", arg0, arg1] =>
      return .Pmov_rr (← (dec_Asm_ireg fuel) arg0) (← (dec_Asm_ireg fuel) arg1)
    | [.str "Pmovl_ri", arg0, arg1] =>
      return .Pmovl_ri (← (dec_Asm_ireg fuel) arg0) (← (dec_int fuel) arg1)
    | [.str "Pmovq_ri", arg0, arg1] =>
      return .Pmovq_ri (← (dec_Asm_ireg fuel) arg0) (← (dec_long fuel) arg1)
    | [.str "Pmov_rs", arg0, arg1] =>
      return .Pmov_rs (← (dec_Asm_ireg fuel) arg0) (← (dec_pos fuel) arg1)
    | [.str "Pmovl_rm", arg0, arg1] =>
      return .Pmovl_rm (← (dec_Asm_ireg fuel) arg0) (← (dec_Asm_addrmode fuel) arg1)
    | [.str "Pmovq_rm", arg0, arg1] =>
      return .Pmovq_rm (← (dec_Asm_ireg fuel) arg0) (← (dec_Asm_addrmode fuel) arg1)
    | [.str "Pmovl_mr", arg0, arg1] =>
      return .Pmovl_mr (← (dec_Asm_addrmode fuel) arg0) (← (dec_Asm_ireg fuel) arg1)
    | [.str "Pmovq_mr", arg0, arg1] =>
      return .Pmovq_mr (← (dec_Asm_addrmode fuel) arg0) (← (dec_Asm_ireg fuel) arg1)
    | [.str "Pmovsd_ff", arg0, arg1] =>
      return .Pmovsd_ff (← (dec_Asm_freg fuel) arg0) (← (dec_Asm_freg fuel) arg1)
    | [.str "Pmovsd_fi", arg0, arg1] =>
      return .Pmovsd_fi (← (dec_Asm_freg fuel) arg0) (← (dec_float fuel) arg1)
    | [.str "Pmovsd_fm", arg0, arg1] =>
      return .Pmovsd_fm (← (dec_Asm_freg fuel) arg0) (← (dec_Asm_addrmode fuel) arg1)
    | [.str "Pmovsd_mf", arg0, arg1] =>
      return .Pmovsd_mf (← (dec_Asm_addrmode fuel) arg0) (← (dec_Asm_freg fuel) arg1)
    | [.str "Pmovss_fi", arg0, arg1] =>
      return .Pmovss_fi (← (dec_Asm_freg fuel) arg0) (← (dec_single fuel) arg1)
    | [.str "Pmovss_fm", arg0, arg1] =>
      return .Pmovss_fm (← (dec_Asm_freg fuel) arg0) (← (dec_Asm_addrmode fuel) arg1)
    | [.str "Pmovss_mf", arg0, arg1] =>
      return .Pmovss_mf (← (dec_Asm_addrmode fuel) arg0) (← (dec_Asm_freg fuel) arg1)
    | [.str "Pfldl_m", arg0] =>
      return .Pfldl_m (← (dec_Asm_addrmode fuel) arg0)
    | [.str "Pfstpl_m", arg0] =>
      return .Pfstpl_m (← (dec_Asm_addrmode fuel) arg0)
    | [.str "Pflds_m", arg0] =>
      return .Pflds_m (← (dec_Asm_addrmode fuel) arg0)
    | [.str "Pfstps_m", arg0] =>
      return .Pfstps_m (← (dec_Asm_addrmode fuel) arg0)
    | [.str "Pmovb_mr", arg0, arg1] =>
      return .Pmovb_mr (← (dec_Asm_addrmode fuel) arg0) (← (dec_Asm_ireg fuel) arg1)
    | [.str "Pmovw_mr", arg0, arg1] =>
      return .Pmovw_mr (← (dec_Asm_addrmode fuel) arg0) (← (dec_Asm_ireg fuel) arg1)
    | [.str "Pmovzb_rr", arg0, arg1] =>
      return .Pmovzb_rr (← (dec_Asm_ireg fuel) arg0) (← (dec_Asm_ireg fuel) arg1)
    | [.str "Pmovzb_rm", arg0, arg1] =>
      return .Pmovzb_rm (← (dec_Asm_ireg fuel) arg0) (← (dec_Asm_addrmode fuel) arg1)
    | [.str "Pmovsb_rr", arg0, arg1] =>
      return .Pmovsb_rr (← (dec_Asm_ireg fuel) arg0) (← (dec_Asm_ireg fuel) arg1)
    | [.str "Pmovsb_rm", arg0, arg1] =>
      return .Pmovsb_rm (← (dec_Asm_ireg fuel) arg0) (← (dec_Asm_addrmode fuel) arg1)
    | [.str "Pmovzw_rr", arg0, arg1] =>
      return .Pmovzw_rr (← (dec_Asm_ireg fuel) arg0) (← (dec_Asm_ireg fuel) arg1)
    | [.str "Pmovzw_rm", arg0, arg1] =>
      return .Pmovzw_rm (← (dec_Asm_ireg fuel) arg0) (← (dec_Asm_addrmode fuel) arg1)
    | [.str "Pmovsw_rr", arg0, arg1] =>
      return .Pmovsw_rr (← (dec_Asm_ireg fuel) arg0) (← (dec_Asm_ireg fuel) arg1)
    | [.str "Pmovsw_rm", arg0, arg1] =>
      return .Pmovsw_rm (← (dec_Asm_ireg fuel) arg0) (← (dec_Asm_addrmode fuel) arg1)
    | [.str "Pmovzl_rr", arg0, arg1] =>
      return .Pmovzl_rr (← (dec_Asm_ireg fuel) arg0) (← (dec_Asm_ireg fuel) arg1)
    | [.str "Pmovsl_rr", arg0, arg1] =>
      return .Pmovsl_rr (← (dec_Asm_ireg fuel) arg0) (← (dec_Asm_ireg fuel) arg1)
    | [.str "Pmovls_rr", arg0] =>
      return .Pmovls_rr (← (dec_Asm_ireg fuel) arg0)
    | [.str "Pcvtsd2ss_ff", arg0, arg1] =>
      return .Pcvtsd2ss_ff (← (dec_Asm_freg fuel) arg0) (← (dec_Asm_freg fuel) arg1)
    | [.str "Pcvtss2sd_ff", arg0, arg1] =>
      return .Pcvtss2sd_ff (← (dec_Asm_freg fuel) arg0) (← (dec_Asm_freg fuel) arg1)
    | [.str "Pcvttsd2si_rf", arg0, arg1] =>
      return .Pcvttsd2si_rf (← (dec_Asm_ireg fuel) arg0) (← (dec_Asm_freg fuel) arg1)
    | [.str "Pcvtsi2sd_fr", arg0, arg1] =>
      return .Pcvtsi2sd_fr (← (dec_Asm_freg fuel) arg0) (← (dec_Asm_ireg fuel) arg1)
    | [.str "Pcvttss2si_rf", arg0, arg1] =>
      return .Pcvttss2si_rf (← (dec_Asm_ireg fuel) arg0) (← (dec_Asm_freg fuel) arg1)
    | [.str "Pcvtsi2ss_fr", arg0, arg1] =>
      return .Pcvtsi2ss_fr (← (dec_Asm_freg fuel) arg0) (← (dec_Asm_ireg fuel) arg1)
    | [.str "Pcvttsd2sl_rf", arg0, arg1] =>
      return .Pcvttsd2sl_rf (← (dec_Asm_ireg fuel) arg0) (← (dec_Asm_freg fuel) arg1)
    | [.str "Pcvtsl2sd_fr", arg0, arg1] =>
      return .Pcvtsl2sd_fr (← (dec_Asm_freg fuel) arg0) (← (dec_Asm_ireg fuel) arg1)
    | [.str "Pcvttss2sl_rf", arg0, arg1] =>
      return .Pcvttss2sl_rf (← (dec_Asm_ireg fuel) arg0) (← (dec_Asm_freg fuel) arg1)
    | [.str "Pcvtsl2ss_fr", arg0, arg1] =>
      return .Pcvtsl2ss_fr (← (dec_Asm_freg fuel) arg0) (← (dec_Asm_ireg fuel) arg1)
    | [.str "Pleal", arg0, arg1] =>
      return .Pleal (← (dec_Asm_ireg fuel) arg0) (← (dec_Asm_addrmode fuel) arg1)
    | [.str "Pleaq", arg0, arg1] =>
      return .Pleaq (← (dec_Asm_ireg fuel) arg0) (← (dec_Asm_addrmode fuel) arg1)
    | [.str "Pnegl", arg0] =>
      return .Pnegl (← (dec_Asm_ireg fuel) arg0)
    | [.str "Pnegq", arg0] =>
      return .Pnegq (← (dec_Asm_ireg fuel) arg0)
    | [.str "Paddl_ri", arg0, arg1] =>
      return .Paddl_ri (← (dec_Asm_ireg fuel) arg0) (← (dec_int fuel) arg1)
    | [.str "Paddq_ri", arg0, arg1] =>
      return .Paddq_ri (← (dec_Asm_ireg fuel) arg0) (← (dec_long fuel) arg1)
    | [.str "Psubl_rr", arg0, arg1] =>
      return .Psubl_rr (← (dec_Asm_ireg fuel) arg0) (← (dec_Asm_ireg fuel) arg1)
    | [.str "Psubq_rr", arg0, arg1] =>
      return .Psubq_rr (← (dec_Asm_ireg fuel) arg0) (← (dec_Asm_ireg fuel) arg1)
    | [.str "Pimull_rr", arg0, arg1] =>
      return .Pimull_rr (← (dec_Asm_ireg fuel) arg0) (← (dec_Asm_ireg fuel) arg1)
    | [.str "Pimulq_rr", arg0, arg1] =>
      return .Pimulq_rr (← (dec_Asm_ireg fuel) arg0) (← (dec_Asm_ireg fuel) arg1)
    | [.str "Pimull_ri", arg0, arg1] =>
      return .Pimull_ri (← (dec_Asm_ireg fuel) arg0) (← (dec_int fuel) arg1)
    | [.str "Pimulq_ri", arg0, arg1] =>
      return .Pimulq_ri (← (dec_Asm_ireg fuel) arg0) (← (dec_long fuel) arg1)
    | [.str "Pimull_r", arg0] =>
      return .Pimull_r (← (dec_Asm_ireg fuel) arg0)
    | [.str "Pimulq_r", arg0] =>
      return .Pimulq_r (← (dec_Asm_ireg fuel) arg0)
    | [.str "Pmull_r", arg0] =>
      return .Pmull_r (← (dec_Asm_ireg fuel) arg0)
    | [.str "Pmulq_r", arg0] =>
      return .Pmulq_r (← (dec_Asm_ireg fuel) arg0)
    | [.str "Pcltd"] =>
      return .Pcltd
    | [.str "Pcqto"] =>
      return .Pcqto
    | [.str "Pdivl", arg0] =>
      return .Pdivl (← (dec_Asm_ireg fuel) arg0)
    | [.str "Pdivq", arg0] =>
      return .Pdivq (← (dec_Asm_ireg fuel) arg0)
    | [.str "Pidivl", arg0] =>
      return .Pidivl (← (dec_Asm_ireg fuel) arg0)
    | [.str "Pidivq", arg0] =>
      return .Pidivq (← (dec_Asm_ireg fuel) arg0)
    | [.str "Pandl_rr", arg0, arg1] =>
      return .Pandl_rr (← (dec_Asm_ireg fuel) arg0) (← (dec_Asm_ireg fuel) arg1)
    | [.str "Pandq_rr", arg0, arg1] =>
      return .Pandq_rr (← (dec_Asm_ireg fuel) arg0) (← (dec_Asm_ireg fuel) arg1)
    | [.str "Pandl_ri", arg0, arg1] =>
      return .Pandl_ri (← (dec_Asm_ireg fuel) arg0) (← (dec_int fuel) arg1)
    | [.str "Pandq_ri", arg0, arg1] =>
      return .Pandq_ri (← (dec_Asm_ireg fuel) arg0) (← (dec_long fuel) arg1)
    | [.str "Porl_rr", arg0, arg1] =>
      return .Porl_rr (← (dec_Asm_ireg fuel) arg0) (← (dec_Asm_ireg fuel) arg1)
    | [.str "Porq_rr", arg0, arg1] =>
      return .Porq_rr (← (dec_Asm_ireg fuel) arg0) (← (dec_Asm_ireg fuel) arg1)
    | [.str "Porl_ri", arg0, arg1] =>
      return .Porl_ri (← (dec_Asm_ireg fuel) arg0) (← (dec_int fuel) arg1)
    | [.str "Porq_ri", arg0, arg1] =>
      return .Porq_ri (← (dec_Asm_ireg fuel) arg0) (← (dec_long fuel) arg1)
    | [.str "Pxorl_r", arg0] =>
      return .Pxorl_r (← (dec_Asm_ireg fuel) arg0)
    | [.str "Pxorq_r", arg0] =>
      return .Pxorq_r (← (dec_Asm_ireg fuel) arg0)
    | [.str "Pxorl_rr", arg0, arg1] =>
      return .Pxorl_rr (← (dec_Asm_ireg fuel) arg0) (← (dec_Asm_ireg fuel) arg1)
    | [.str "Pxorq_rr", arg0, arg1] =>
      return .Pxorq_rr (← (dec_Asm_ireg fuel) arg0) (← (dec_Asm_ireg fuel) arg1)
    | [.str "Pxorl_ri", arg0, arg1] =>
      return .Pxorl_ri (← (dec_Asm_ireg fuel) arg0) (← (dec_int fuel) arg1)
    | [.str "Pxorq_ri", arg0, arg1] =>
      return .Pxorq_ri (← (dec_Asm_ireg fuel) arg0) (← (dec_long fuel) arg1)
    | [.str "Pnotl", arg0] =>
      return .Pnotl (← (dec_Asm_ireg fuel) arg0)
    | [.str "Pnotq", arg0] =>
      return .Pnotq (← (dec_Asm_ireg fuel) arg0)
    | [.str "Psall_rcl", arg0] =>
      return .Psall_rcl (← (dec_Asm_ireg fuel) arg0)
    | [.str "Psalq_rcl", arg0] =>
      return .Psalq_rcl (← (dec_Asm_ireg fuel) arg0)
    | [.str "Psall_ri", arg0, arg1] =>
      return .Psall_ri (← (dec_Asm_ireg fuel) arg0) (← (dec_int fuel) arg1)
    | [.str "Psalq_ri", arg0, arg1] =>
      return .Psalq_ri (← (dec_Asm_ireg fuel) arg0) (← (dec_int fuel) arg1)
    | [.str "Pshrl_rcl", arg0] =>
      return .Pshrl_rcl (← (dec_Asm_ireg fuel) arg0)
    | [.str "Pshrq_rcl", arg0] =>
      return .Pshrq_rcl (← (dec_Asm_ireg fuel) arg0)
    | [.str "Pshrl_ri", arg0, arg1] =>
      return .Pshrl_ri (← (dec_Asm_ireg fuel) arg0) (← (dec_int fuel) arg1)
    | [.str "Pshrq_ri", arg0, arg1] =>
      return .Pshrq_ri (← (dec_Asm_ireg fuel) arg0) (← (dec_int fuel) arg1)
    | [.str "Psarl_rcl", arg0] =>
      return .Psarl_rcl (← (dec_Asm_ireg fuel) arg0)
    | [.str "Psarq_rcl", arg0] =>
      return .Psarq_rcl (← (dec_Asm_ireg fuel) arg0)
    | [.str "Psarl_ri", arg0, arg1] =>
      return .Psarl_ri (← (dec_Asm_ireg fuel) arg0) (← (dec_int fuel) arg1)
    | [.str "Psarq_ri", arg0, arg1] =>
      return .Psarq_ri (← (dec_Asm_ireg fuel) arg0) (← (dec_int fuel) arg1)
    | [.str "Pshld_ri", arg0, arg1, arg2] =>
      return .Pshld_ri (← (dec_Asm_ireg fuel) arg0) (← (dec_Asm_ireg fuel) arg1) (← (dec_int fuel) arg2)
    | [.str "Prorl_ri", arg0, arg1] =>
      return .Prorl_ri (← (dec_Asm_ireg fuel) arg0) (← (dec_int fuel) arg1)
    | [.str "Prorq_ri", arg0, arg1] =>
      return .Prorq_ri (← (dec_Asm_ireg fuel) arg0) (← (dec_int fuel) arg1)
    | [.str "Pcmpl_rr", arg0, arg1] =>
      return .Pcmpl_rr (← (dec_Asm_ireg fuel) arg0) (← (dec_Asm_ireg fuel) arg1)
    | [.str "Pcmpq_rr", arg0, arg1] =>
      return .Pcmpq_rr (← (dec_Asm_ireg fuel) arg0) (← (dec_Asm_ireg fuel) arg1)
    | [.str "Pcmpl_ri", arg0, arg1] =>
      return .Pcmpl_ri (← (dec_Asm_ireg fuel) arg0) (← (dec_int fuel) arg1)
    | [.str "Pcmpq_ri", arg0, arg1] =>
      return .Pcmpq_ri (← (dec_Asm_ireg fuel) arg0) (← (dec_long fuel) arg1)
    | [.str "Ptestl_rr", arg0, arg1] =>
      return .Ptestl_rr (← (dec_Asm_ireg fuel) arg0) (← (dec_Asm_ireg fuel) arg1)
    | [.str "Ptestq_rr", arg0, arg1] =>
      return .Ptestq_rr (← (dec_Asm_ireg fuel) arg0) (← (dec_Asm_ireg fuel) arg1)
    | [.str "Ptestl_ri", arg0, arg1] =>
      return .Ptestl_ri (← (dec_Asm_ireg fuel) arg0) (← (dec_int fuel) arg1)
    | [.str "Ptestq_ri", arg0, arg1] =>
      return .Ptestq_ri (← (dec_Asm_ireg fuel) arg0) (← (dec_long fuel) arg1)
    | [.str "Pcmov", arg0, arg1, arg2] =>
      return .Pcmov (← (dec_Asm_testcond fuel) arg0) (← (dec_Asm_ireg fuel) arg1) (← (dec_Asm_ireg fuel) arg2)
    | [.str "Psetcc", arg0, arg1] =>
      return .Psetcc (← (dec_Asm_testcond fuel) arg0) (← (dec_Asm_ireg fuel) arg1)
    | [.str "Paddd_ff", arg0, arg1] =>
      return .Paddd_ff (← (dec_Asm_freg fuel) arg0) (← (dec_Asm_freg fuel) arg1)
    | [.str "Psubd_ff", arg0, arg1] =>
      return .Psubd_ff (← (dec_Asm_freg fuel) arg0) (← (dec_Asm_freg fuel) arg1)
    | [.str "Pmuld_ff", arg0, arg1] =>
      return .Pmuld_ff (← (dec_Asm_freg fuel) arg0) (← (dec_Asm_freg fuel) arg1)
    | [.str "Pdivd_ff", arg0, arg1] =>
      return .Pdivd_ff (← (dec_Asm_freg fuel) arg0) (← (dec_Asm_freg fuel) arg1)
    | [.str "Pnegd", arg0] =>
      return .Pnegd (← (dec_Asm_freg fuel) arg0)
    | [.str "Pabsd", arg0] =>
      return .Pabsd (← (dec_Asm_freg fuel) arg0)
    | [.str "Pcomisd_ff", arg0, arg1] =>
      return .Pcomisd_ff (← (dec_Asm_freg fuel) arg0) (← (dec_Asm_freg fuel) arg1)
    | [.str "Pxorpd_f", arg0] =>
      return .Pxorpd_f (← (dec_Asm_freg fuel) arg0)
    | [.str "Padds_ff", arg0, arg1] =>
      return .Padds_ff (← (dec_Asm_freg fuel) arg0) (← (dec_Asm_freg fuel) arg1)
    | [.str "Psubs_ff", arg0, arg1] =>
      return .Psubs_ff (← (dec_Asm_freg fuel) arg0) (← (dec_Asm_freg fuel) arg1)
    | [.str "Pmuls_ff", arg0, arg1] =>
      return .Pmuls_ff (← (dec_Asm_freg fuel) arg0) (← (dec_Asm_freg fuel) arg1)
    | [.str "Pdivs_ff", arg0, arg1] =>
      return .Pdivs_ff (← (dec_Asm_freg fuel) arg0) (← (dec_Asm_freg fuel) arg1)
    | [.str "Pnegs", arg0] =>
      return .Pnegs (← (dec_Asm_freg fuel) arg0)
    | [.str "Pabss", arg0] =>
      return .Pabss (← (dec_Asm_freg fuel) arg0)
    | [.str "Pcomiss_ff", arg0, arg1] =>
      return .Pcomiss_ff (← (dec_Asm_freg fuel) arg0) (← (dec_Asm_freg fuel) arg1)
    | [.str "Pxorps_f", arg0] =>
      return .Pxorps_f (← (dec_Asm_freg fuel) arg0)
    | [.str "Pjmp_l", arg0] =>
      return .Pjmp_l (← (dec_pos fuel) arg0)
    | [.str "Pjmp_s", arg0, arg1] =>
      return .Pjmp_s (← (dec_pos fuel) arg0) (← (dec_AST_signature fuel) arg1)
    | [.str "Pjmp_r", arg0, arg1] =>
      return .Pjmp_r (← (dec_Asm_ireg fuel) arg0) (← (dec_AST_signature fuel) arg1)
    | [.str "Pjcc", arg0, arg1] =>
      return .Pjcc (← (dec_Asm_testcond fuel) arg0) (← (dec_pos fuel) arg1)
    | [.str "Pjcc2", arg0, arg1, arg2] =>
      return .Pjcc2 (← (dec_Asm_testcond fuel) arg0) (← (dec_Asm_testcond fuel) arg1) (← (dec_pos fuel) arg2)
    | [.str "Pjmptbl", arg0, arg1] =>
      return .Pjmptbl (← (dec_Asm_ireg fuel) arg0) (← (decList (dec_pos fuel)) arg1)
    | [.str "Pcall_s", arg0, arg1] =>
      return .Pcall_s (← (dec_pos fuel) arg0) (← (dec_AST_signature fuel) arg1)
    | [.str "Pcall_r", arg0, arg1] =>
      return .Pcall_r (← (dec_Asm_ireg fuel) arg0) (← (dec_AST_signature fuel) arg1)
    | [.str "Pret"] =>
      return .Pret
    | [.str "Pmov_rm_a", arg0, arg1] =>
      return .Pmov_rm_a (← (dec_Asm_ireg fuel) arg0) (← (dec_Asm_addrmode fuel) arg1)
    | [.str "Pmov_mr_a", arg0, arg1] =>
      return .Pmov_mr_a (← (dec_Asm_addrmode fuel) arg0) (← (dec_Asm_ireg fuel) arg1)
    | [.str "Pmovsd_fm_a", arg0, arg1] =>
      return .Pmovsd_fm_a (← (dec_Asm_freg fuel) arg0) (← (dec_Asm_addrmode fuel) arg1)
    | [.str "Pmovsd_mf_a", arg0, arg1] =>
      return .Pmovsd_mf_a (← (dec_Asm_addrmode fuel) arg0) (← (dec_Asm_freg fuel) arg1)
    | [.str "Plabel", arg0] =>
      return .Plabel (← (dec_pos fuel) arg0)
    | [.str "Pallocframe", arg0, arg1, arg2] =>
      return .Pallocframe (← (dec_z fuel) arg0) (← (dec_ptr fuel) arg1) (← (dec_ptr fuel) arg2)
    | [.str "Pfreeframe", arg0, arg1, arg2] =>
      return .Pfreeframe (← (dec_z fuel) arg0) (← (dec_ptr fuel) arg1) (← (dec_ptr fuel) arg2)
    | [.str "Pbuiltin", arg0, arg1, arg2] =>
      return .Pbuiltin (← (dec_AST_external_function fuel) arg0) (← (decList (dec_A_builtin_arg fuel)) arg1) (← (dec_A_builtin_res fuel) arg2)
    | [.str "Padcl_ri", arg0, arg1] =>
      return .Padcl_ri (← (dec_Asm_ireg fuel) arg0) (← (dec_int fuel) arg1)
    | [.str "Padcl_rr", arg0, arg1] =>
      return .Padcl_rr (← (dec_Asm_ireg fuel) arg0) (← (dec_Asm_ireg fuel) arg1)
    | [.str "Paddl_mi", arg0, arg1] =>
      return .Paddl_mi (← (dec_Asm_addrmode fuel) arg0) (← (dec_int fuel) arg1)
    | [.str "Paddl_rr", arg0, arg1] =>
      return .Paddl_rr (← (dec_Asm_ireg fuel) arg0) (← (dec_Asm_ireg fuel) arg1)
    | [.str "Pbsfl", arg0, arg1] =>
      return .Pbsfl (← (dec_Asm_ireg fuel) arg0) (← (dec_Asm_ireg fuel) arg1)
    | [.str "Pbsfq", arg0, arg1] =>
      return .Pbsfq (← (dec_Asm_ireg fuel) arg0) (← (dec_Asm_ireg fuel) arg1)
    | [.str "Pbsrl", arg0, arg1] =>
      return .Pbsrl (← (dec_Asm_ireg fuel) arg0) (← (dec_Asm_ireg fuel) arg1)
    | [.str "Pbsrq", arg0, arg1] =>
      return .Pbsrq (← (dec_Asm_ireg fuel) arg0) (← (dec_Asm_ireg fuel) arg1)
    | [.str "Pbswap64", arg0] =>
      return .Pbswap64 (← (dec_Asm_ireg fuel) arg0)
    | [.str "Pbswap32", arg0] =>
      return .Pbswap32 (← (dec_Asm_ireg fuel) arg0)
    | [.str "Pbswap16", arg0] =>
      return .Pbswap16 (← (dec_Asm_ireg fuel) arg0)
    | [.str "Pcfi_adjust", arg0] =>
      return .Pcfi_adjust (← (dec_int fuel) arg0)
    | [.str "Pfmadd132", arg0, arg1, arg2] =>
      return .Pfmadd132 (← (dec_Asm_freg fuel) arg0) (← (dec_Asm_freg fuel) arg1) (← (dec_Asm_freg fuel) arg2)
    | [.str "Pfmadd213", arg0, arg1, arg2] =>
      return .Pfmadd213 (← (dec_Asm_freg fuel) arg0) (← (dec_Asm_freg fuel) arg1) (← (dec_Asm_freg fuel) arg2)
    | [.str "Pfmadd231", arg0, arg1, arg2] =>
      return .Pfmadd231 (← (dec_Asm_freg fuel) arg0) (← (dec_Asm_freg fuel) arg1) (← (dec_Asm_freg fuel) arg2)
    | [.str "Pfmsub132", arg0, arg1, arg2] =>
      return .Pfmsub132 (← (dec_Asm_freg fuel) arg0) (← (dec_Asm_freg fuel) arg1) (← (dec_Asm_freg fuel) arg2)
    | [.str "Pfmsub213", arg0, arg1, arg2] =>
      return .Pfmsub213 (← (dec_Asm_freg fuel) arg0) (← (dec_Asm_freg fuel) arg1) (← (dec_Asm_freg fuel) arg2)
    | [.str "Pfmsub231", arg0, arg1, arg2] =>
      return .Pfmsub231 (← (dec_Asm_freg fuel) arg0) (← (dec_Asm_freg fuel) arg1) (← (dec_Asm_freg fuel) arg2)
    | [.str "Pfnmadd132", arg0, arg1, arg2] =>
      return .Pfnmadd132 (← (dec_Asm_freg fuel) arg0) (← (dec_Asm_freg fuel) arg1) (← (dec_Asm_freg fuel) arg2)
    | [.str "Pfnmadd213", arg0, arg1, arg2] =>
      return .Pfnmadd213 (← (dec_Asm_freg fuel) arg0) (← (dec_Asm_freg fuel) arg1) (← (dec_Asm_freg fuel) arg2)
    | [.str "Pfnmadd231", arg0, arg1, arg2] =>
      return .Pfnmadd231 (← (dec_Asm_freg fuel) arg0) (← (dec_Asm_freg fuel) arg1) (← (dec_Asm_freg fuel) arg2)
    | [.str "Pfnmsub132", arg0, arg1, arg2] =>
      return .Pfnmsub132 (← (dec_Asm_freg fuel) arg0) (← (dec_Asm_freg fuel) arg1) (← (dec_Asm_freg fuel) arg2)
    | [.str "Pfnmsub213", arg0, arg1, arg2] =>
      return .Pfnmsub213 (← (dec_Asm_freg fuel) arg0) (← (dec_Asm_freg fuel) arg1) (← (dec_Asm_freg fuel) arg2)
    | [.str "Pfnmsub231", arg0, arg1, arg2] =>
      return .Pfnmsub231 (← (dec_Asm_freg fuel) arg0) (← (dec_Asm_freg fuel) arg1) (← (dec_Asm_freg fuel) arg2)
    | [.str "Pmaxsd", arg0, arg1] =>
      return .Pmaxsd (← (dec_Asm_freg fuel) arg0) (← (dec_Asm_freg fuel) arg1)
    | [.str "Pminsd", arg0, arg1] =>
      return .Pminsd (← (dec_Asm_freg fuel) arg0) (← (dec_Asm_freg fuel) arg1)
    | [.str "Pmovb_rm", arg0, arg1] =>
      return .Pmovb_rm (← (dec_Asm_ireg fuel) arg0) (← (dec_Asm_addrmode fuel) arg1)
    | [.str "Pmovq_rf", arg0, arg1] =>
      return .Pmovq_rf (← (dec_Asm_ireg fuel) arg0) (← (dec_Asm_freg fuel) arg1)
    | [.str "Pmovsq_mr", arg0, arg1] =>
      return .Pmovsq_mr (← (dec_Asm_addrmode fuel) arg0) (← (dec_Asm_freg fuel) arg1)
    | [.str "Pmovsq_rm", arg0, arg1] =>
      return .Pmovsq_rm (← (dec_Asm_freg fuel) arg0) (← (dec_Asm_addrmode fuel) arg1)
    | [.str "Pmovsb"] =>
      return .Pmovsb
    | [.str "Pmovsw"] =>
      return .Pmovsw
    | [.str "Pmovw_rm", arg0, arg1] =>
      return .Pmovw_rm (← (dec_Asm_ireg fuel) arg0) (← (dec_Asm_addrmode fuel) arg1)
    | [.str "Pnop"] =>
      return .Pnop
    | [.str "Prep_movsl"] =>
      return .Prep_movsl
    | [.str "Psbbl_rr", arg0, arg1] =>
      return .Psbbl_rr (← (dec_Asm_ireg fuel) arg0) (← (dec_Asm_ireg fuel) arg1)
    | [.str "Psqrtsd", arg0, arg1] =>
      return .Psqrtsd (← (dec_Asm_freg fuel) arg0) (← (dec_Asm_freg fuel) arg1)
    | [.str "Psubl_ri", arg0, arg1] =>
      return .Psubl_ri (← (dec_Asm_ireg fuel) arg0) (← (dec_int fuel) arg1)
    | [.str "Psubq_ri", arg0, arg1] =>
      return .Psubq_ri (← (dec_Asm_ireg fuel) arg0) (← (dec_long fuel) arg1)
    | _ => throw "invalid Asm_instruction constructor or arity"

def dec_Asm_coq_function : Nat → Json → CodecResult (X86.Asm.function)
  | 0, _ => throw "interchange depth exceeded"
  | fuel + 1, value => do
    match ← fields value with
    | [.str "Asm_coq_function", arg0, arg1] =>
      return { fn_sig := (← (dec_AST_signature fuel) arg0), fn_code := (← (decList (dec_Asm_instruction fuel)) arg1) }
    | _ => throw "invalid Asm_coq_function constructor or arity"

def dec_CFundef : Nat → Json → CodecResult (Cfrontend.Ctypes.fundef (Cfrontend.Csyntax.function))
  | 0, _ => throw "interchange depth exceeded"
  | fuel + 1, value => do
    let values ← value.getArr?
    if size : values.size = 2 then
      match values[0] with
      | .str "Internal" =>
        return .Internal (← (dec_Csyntax_coq_function fuel) values[1])
      | _ => throw "invalid CFundef constructor or arity"
    else if size : values.size = 5 then
      match values[0] with
      | .str "External" =>
        return .External (← (dec_AST_external_function fuel) values[1]) (← (decList (dec_Ctypes_coq_type fuel)) values[2]) (← (dec_Ctypes_coq_type fuel) values[3]) (← (dec_AST_calling_convention fuel) values[4])
      | _ => throw "invalid CFundef constructor or arity"
    else throw "invalid CFundef constructor or arity"

def dec_CGlobvar : Nat → Json → CodecResult (Common.AST.globvar (Cfrontend.Ctypes.type))
  | 0, _ => throw "interchange depth exceeded"
  | fuel + 1, value => do
    let values ← value.getArr?
    if size : values.size = 5 then
      match values[0] with
      | .str "CGlobvar" =>
        return { gvar_info := (← (dec_Ctypes_coq_type fuel) values[1]), gvar_init := (← (decList (dec_AST_init_data fuel)) values[2]), gvar_readonly := (← (dec_bool fuel) values[3]), gvar_volatile := (← (dec_bool fuel) values[4]) }
      | _ => throw "invalid CGlobvar constructor or arity"
    else throw "invalid CGlobvar constructor or arity"

def dec_CGlobdef : Nat → Json → CodecResult (Common.AST.globdef (Cfrontend.Ctypes.fundef (Cfrontend.Csyntax.function)) (Cfrontend.Ctypes.type))
  | 0, _ => throw "interchange depth exceeded"
  | fuel + 1, value => do
    let values ← value.getArr?
    if size : values.size = 2 then
      match values[0] with
      | .str "Gfun" =>
        return .Gfun (← (dec_CFundef fuel) values[1])
      | .str "Gvar" =>
        return .Gvar (← (dec_CGlobvar fuel) values[1])
      | _ => throw "invalid CGlobdef constructor or arity"
    else throw "invalid CGlobdef constructor or arity"

def dec_AFundef : Nat → Json → CodecResult (Common.AST.fundef (X86.Asm.function))
  | 0, _ => throw "interchange depth exceeded"
  | fuel + 1, value => do
    match ← fields value with
    | [.str "Internal", arg0] =>
      return .Internal (← (dec_Asm_coq_function fuel) arg0)
    | [.str "External", arg0] =>
      return .External (← (dec_AST_external_function fuel) arg0)
    | _ => throw "invalid AFundef constructor or arity"

def dec_AGlobvar : Nat → Json → CodecResult (Common.AST.globvar (Unit))
  | 0, _ => throw "interchange depth exceeded"
  | fuel + 1, value => do
    match ← fields value with
    | [.str "AGlobvar", arg0, arg1, arg2, arg3] =>
      return { gvar_info := (← (dec_unit fuel) arg0), gvar_init := (← (decList (dec_AST_init_data fuel)) arg1), gvar_readonly := (← (dec_bool fuel) arg2), gvar_volatile := (← (dec_bool fuel) arg3) }
    | _ => throw "invalid AGlobvar constructor or arity"

def dec_AGlobdef : Nat → Json → CodecResult (Common.AST.globdef (Common.AST.fundef (X86.Asm.function)) (Unit))
  | 0, _ => throw "interchange depth exceeded"
  | fuel + 1, value => do
    match ← fields value with
    | [.str "Gfun", arg0] =>
      return .Gfun (← (dec_AFundef fuel) arg0)
    | [.str "Gvar", arg0] =>
      return .Gvar (← (dec_AGlobvar fuel) arg0)
    | _ => throw "invalid AGlobdef constructor or arity"

def dec_AProgram : Nat → Json → CodecResult (X86.Asm.program)
  | 0, _ => throw "interchange depth exceeded"
  | fuel + 1, value => do
    match ← fields value with
    | [.str "AProgram", arg0, arg1, arg2] =>
      return { prog_defs := (← (decList (decPair (dec_pos fuel) (dec_AGlobdef fuel))) arg0), prog_public := (← (decList (dec_pos fuel)) arg1), prog_main := (← (dec_pos fuel) arg2) }
    | _ => throw "invalid AProgram constructor or arity"

def dec_A_builtin_arg : Nat → Json → CodecResult (Common.AST.builtin_arg X86.Asm.preg)
  | 0, _ => throw "interchange depth exceeded"
  | fuel + 1, value => do
    match ← fields value with
    | [.str "BA", arg0] =>
      return .BA (← (dec_Asm_preg fuel) arg0)
    | [.str "BA_int", arg0] =>
      return .BA_int (← (dec_int fuel) arg0)
    | [.str "BA_long", arg0] =>
      return .BA_long (← (dec_long fuel) arg0)
    | [.str "BA_float", arg0] =>
      return .BA_float (← (dec_float fuel) arg0)
    | [.str "BA_single", arg0] =>
      return .BA_single (← (dec_single fuel) arg0)
    | [.str "BA_loadstack", arg0, arg1] =>
      return .BA_loadstack (← (dec_AST_memory_chunk fuel) arg0) (← (dec_ptr fuel) arg1)
    | [.str "BA_addrstack", arg0] =>
      return .BA_addrstack (← (dec_ptr fuel) arg0)
    | [.str "BA_loadglobal", arg0, arg1, arg2] =>
      return .BA_loadglobal (← (dec_AST_memory_chunk fuel) arg0) (← (dec_pos fuel) arg1) (← (dec_ptr fuel) arg2)
    | [.str "BA_addrglobal", arg0, arg1] =>
      return .BA_addrglobal (← (dec_pos fuel) arg0) (← (dec_ptr fuel) arg1)
    | [.str "BA_splitlong", arg0, arg1] =>
      return .BA_splitlong (← (dec_A_builtin_arg fuel) arg0) (← (dec_A_builtin_arg fuel) arg1)
    | [.str "BA_addptr", arg0, arg1] =>
      return .BA_addptr (← (dec_A_builtin_arg fuel) arg0) (← (dec_A_builtin_arg fuel) arg1)
    | _ => throw "invalid A_builtin_arg constructor or arity"

def dec_A_builtin_res : Nat → Json → CodecResult (Common.AST.builtin_res X86.Asm.preg)
  | 0, _ => throw "interchange depth exceeded"
  | fuel + 1, value => do
    match ← fields value with
    | [.str "BR", arg0] =>
      return .BR (← (dec_Asm_preg fuel) arg0)
    | [.str "BR_none"] =>
      return .BR_none
    | [.str "BR_splitlong", arg0, arg1] =>
      return .BR_splitlong (← (dec_A_builtin_res fuel) arg0) (← (dec_A_builtin_res fuel) arg1)
    | _ => throw "invalid A_builtin_res constructor or arity"

end

end CompCert4Lean.Prototype
