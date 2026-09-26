import CompCert4Lean.Prototype.Codecs

open Lean CompCert4Lean CompCert4Lean.Prototype Foundation.Numbers.Rocq.Coq
set_option maxRecDepth 8192
set_option maxHeartbeats 12000000
set_option linter.unusedSimpArgs false
set_option pp.maxSteps 1000

namespace CodecReference
mutual
def dec_AST_typ : Nat → Json → CodecResult (Common.AST.typ)
  | 0, _ => throw "interchange depth exceeded"
  | fuel + 1, value => do
    match ← fields value with
    | [.str "Tint"] =>
      return .Tint
    | [.str "Tfloat"] =>
      return .Tfloat
    | [.str "Tlong"] =>
      return .Tlong
    | [.str "Tsingle"] =>
      return .Tsingle
    | [.str "Tany32"] =>
      return .Tany32
    | [.str "Tany64"] =>
      return .Tany64
    | _ => throw "invalid AST_typ constructor or arity"

def dec_AST_xtype : Nat → Json → CodecResult (Common.AST.xtype)
  | 0, _ => throw "interchange depth exceeded"
  | fuel + 1, value => do
    match ← fields value with
    | [.str "Xbool"] =>
      return .Xbool
    | [.str "Xint8signed"] =>
      return .Xint8signed
    | [.str "Xint8unsigned"] =>
      return .Xint8unsigned
    | [.str "Xint16signed"] =>
      return .Xint16signed
    | [.str "Xint16unsigned"] =>
      return .Xint16unsigned
    | [.str "Xint"] =>
      return .Xint
    | [.str "Xfloat"] =>
      return .Xfloat
    | [.str "Xlong"] =>
      return .Xlong
    | [.str "Xsingle"] =>
      return .Xsingle
    | [.str "Xptr"] =>
      return .Xptr
    | [.str "Xany32"] =>
      return .Xany32
    | [.str "Xany64"] =>
      return .Xany64
    | [.str "Xvoid"] =>
      return .Xvoid
    | _ => throw "invalid AST_xtype constructor or arity"

def dec_AST_calling_convention : Nat → Json → CodecResult (Common.AST.calling_convention)
  | 0, _ => throw "interchange depth exceeded"
  | fuel + 1, value => do
    match ← fields value with
    | [.str "AST_calling_convention", arg0, arg1, arg2] =>
      return { cc_vararg := (← (decOption (dec_z fuel)) arg0), cc_unproto := (← (dec_bool fuel) arg1), cc_structret := (← (dec_bool fuel) arg2) }
    | _ => throw "invalid AST_calling_convention constructor or arity"

def dec_AST_signature : Nat → Json → CodecResult (Common.AST.signature)
  | 0, _ => throw "interchange depth exceeded"
  | fuel + 1, value => do
    match ← fields value with
    | [.str "AST_signature", arg0, arg1, arg2] =>
      return { sig_args := (← (decList (dec_AST_xtype fuel)) arg0), sig_res := (← (dec_AST_xtype fuel) arg1), sig_cc := (← (dec_AST_calling_convention fuel) arg2) }
    | _ => throw "invalid AST_signature constructor or arity"

def dec_AST_memory_chunk : Nat → Json → CodecResult (Common.AST.memory_chunk)
  | 0, _ => throw "interchange depth exceeded"
  | fuel + 1, value => do
    match ← fields value with
    | [.str "Mbool"] =>
      return .Mbool
    | [.str "Mint8signed"] =>
      return .Mint8signed
    | [.str "Mint8unsigned"] =>
      return .Mint8unsigned
    | [.str "Mint16signed"] =>
      return .Mint16signed
    | [.str "Mint16unsigned"] =>
      return .Mint16unsigned
    | [.str "Mint32"] =>
      return .Mint32
    | [.str "Mint64"] =>
      return .Mint64
    | [.str "Mfloat32"] =>
      return .Mfloat32
    | [.str "Mfloat64"] =>
      return .Mfloat64
    | [.str "Many32"] =>
      return .Many32
    | [.str "Many64"] =>
      return .Many64
    | _ => throw "invalid AST_memory_chunk constructor or arity"

def dec_AST_init_data : Nat → Json → CodecResult (Common.AST.init_data)
  | 0, _ => throw "interchange depth exceeded"
  | fuel + 1, value => do
    match ← fields value with
    | [.str "Init_int8", arg0] =>
      return .Init_int8 (← (dec_int fuel) arg0)
    | [.str "Init_int16", arg0] =>
      return .Init_int16 (← (dec_int fuel) arg0)
    | [.str "Init_int32", arg0] =>
      return .Init_int32 (← (dec_int fuel) arg0)
    | [.str "Init_int64", arg0] =>
      return .Init_int64 (← (dec_long fuel) arg0)
    | [.str "Init_float32", arg0] =>
      return .Init_float32 (← (dec_single fuel) arg0)
    | [.str "Init_float64", arg0] =>
      return .Init_float64 (← (dec_float fuel) arg0)
    | [.str "Init_space", arg0] =>
      return .Init_space (← (dec_z fuel) arg0)
    | [.str "Init_addrof", arg0, arg1] =>
      return .Init_addrof (← (dec_pos fuel) arg0) (← (dec_ptr fuel) arg1)
    | _ => throw "invalid AST_init_data constructor or arity"

def dec_AST_external_function : Nat → Json → CodecResult (Common.AST.external_function)
  | 0, _ => throw "interchange depth exceeded"
  | fuel + 1, value => do
    match ← fields value with
    | [.str "EF_external", arg0, arg1] =>
      return .EF_external (← (dec_string fuel) arg0) (← (dec_AST_signature fuel) arg1)
    | [.str "EF_builtin", arg0, arg1] =>
      return .EF_builtin (← (dec_string fuel) arg0) (← (dec_AST_signature fuel) arg1)
    | [.str "EF_runtime", arg0, arg1] =>
      return .EF_runtime (← (dec_string fuel) arg0) (← (dec_AST_signature fuel) arg1)
    | [.str "EF_vload", arg0] =>
      return .EF_vload (← (dec_AST_memory_chunk fuel) arg0)
    | [.str "EF_vstore", arg0] =>
      return .EF_vstore (← (dec_AST_memory_chunk fuel) arg0)
    | [.str "EF_malloc"] =>
      return .EF_malloc
    | [.str "EF_free"] =>
      return .EF_free
    | [.str "EF_memcpy", arg0, arg1] =>
      return .EF_memcpy (← (dec_z fuel) arg0) (← (dec_z fuel) arg1)
    | [.str "EF_annot", arg0, arg1, arg2] =>
      return .EF_annot (← (dec_pos fuel) arg0) (← (dec_string fuel) arg1) (← (decList (dec_AST_typ fuel)) arg2)
    | [.str "EF_annot_val", arg0, arg1, arg2] =>
      return .EF_annot_val (← (dec_pos fuel) arg0) (← (dec_string fuel) arg1) (← (dec_AST_typ fuel) arg2)
    | [.str "EF_inline_asm", arg0, arg1, arg2] =>
      return .EF_inline_asm (← (dec_string fuel) arg0) (← (dec_AST_signature fuel) arg1) (← (decList (dec_string fuel)) arg2)
    | [.str "EF_debug", arg0, arg1, arg2] =>
      return .EF_debug (← (dec_pos fuel) arg0) (← (dec_pos fuel) arg1) (← (decList (dec_AST_typ fuel)) arg2)
    | _ => throw "invalid AST_external_function constructor or arity"

def dec_Ctypes_signedness : Nat → Json → CodecResult (Cfrontend.Ctypes.signedness)
  | 0, _ => throw "interchange depth exceeded"
  | fuel + 1, value => do
    match ← fields value with
    | [.str "Signed"] =>
      return .Signed
    | [.str "Unsigned"] =>
      return .Unsigned
    | _ => throw "invalid Ctypes_signedness constructor or arity"

def dec_Ctypes_intsize : Nat → Json → CodecResult (Cfrontend.Ctypes.intsize)
  | 0, _ => throw "interchange depth exceeded"
  | fuel + 1, value => do
    match ← fields value with
    | [.str "I8"] =>
      return .I8
    | [.str "I16"] =>
      return .I16
    | [.str "I32"] =>
      return .I32
    | [.str "IBool"] =>
      return .IBool
    | _ => throw "invalid Ctypes_intsize constructor or arity"

def dec_Ctypes_floatsize : Nat → Json → CodecResult (Cfrontend.Ctypes.floatsize)
  | 0, _ => throw "interchange depth exceeded"
  | fuel + 1, value => do
    match ← fields value with
    | [.str "F32"] =>
      return .F32
    | [.str "F64"] =>
      return .F64
    | _ => throw "invalid Ctypes_floatsize constructor or arity"

def dec_Ctypes_attr : Nat → Json → CodecResult (Cfrontend.Ctypes.attr)
  | 0, _ => throw "interchange depth exceeded"
  | fuel + 1, value => do
    match ← fields value with
    | [.str "Ctypes_attr", arg0, arg1] =>
      return { attr_volatile := (← (dec_bool fuel) arg0), attr_alignas := (← (decOption (dec_n fuel)) arg1) }
    | _ => throw "invalid Ctypes_attr constructor or arity"

def dec_Ctypes_coq_type : Nat → Json → CodecResult (Cfrontend.Ctypes.type)
  | 0, _ => throw "interchange depth exceeded"
  | fuel + 1, value => do
    match ← fields value with
    | [.str "Tvoid"] =>
      return .Tvoid
    | [.str "Tint", arg0, arg1, arg2] =>
      return .Tint (← (dec_Ctypes_intsize fuel) arg0) (← (dec_Ctypes_signedness fuel) arg1) (← (dec_Ctypes_attr fuel) arg2)
    | [.str "Tlong", arg0, arg1] =>
      return .Tlong (← (dec_Ctypes_signedness fuel) arg0) (← (dec_Ctypes_attr fuel) arg1)
    | [.str "Tfloat", arg0, arg1] =>
      return .Tfloat (← (dec_Ctypes_floatsize fuel) arg0) (← (dec_Ctypes_attr fuel) arg1)
    | [.str "Tpointer", arg0, arg1] =>
      return .Tpointer (← (dec_Ctypes_coq_type fuel) arg0) (← (dec_Ctypes_attr fuel) arg1)
    | [.str "Tarray", arg0, arg1, arg2] =>
      return .Tarray (← (dec_Ctypes_coq_type fuel) arg0) (← (dec_z fuel) arg1) (← (dec_Ctypes_attr fuel) arg2)
    | [.str "Tfunction", arg0, arg1, arg2] =>
      return .Tfunction (← (decList (dec_Ctypes_coq_type fuel)) arg0) (← (dec_Ctypes_coq_type fuel) arg1) (← (dec_AST_calling_convention fuel) arg2)
    | [.str "Tstruct", arg0, arg1] =>
      return .Tstruct (← (dec_pos fuel) arg0) (← (dec_Ctypes_attr fuel) arg1)
    | [.str "Tunion", arg0, arg1] =>
      return .Tunion (← (dec_pos fuel) arg0) (← (dec_Ctypes_attr fuel) arg1)
    | _ => throw "invalid Ctypes_coq_type constructor or arity"

def dec_Ctypes_struct_or_union : Nat → Json → CodecResult (Cfrontend.Ctypes.struct_or_union)
  | 0, _ => throw "interchange depth exceeded"
  | fuel + 1, value => do
    match ← fields value with
    | [.str "Struct"] =>
      return .Struct
    | [.str "Union"] =>
      return .Union
    | _ => throw "invalid Ctypes_struct_or_union constructor or arity"

def dec_Ctypes_member : Nat → Json → CodecResult (Cfrontend.Ctypes.member)
  | 0, _ => throw "interchange depth exceeded"
  | fuel + 1, value => do
    match ← fields value with
    | [.str "Member_plain", arg0, arg1] =>
      return .Member_plain (← (dec_pos fuel) arg0) (← (dec_Ctypes_coq_type fuel) arg1)
    | [.str "Member_bitfield", arg0, arg1, arg2, arg3, arg4, arg5] =>
      return .Member_bitfield (← (dec_pos fuel) arg0) (← (dec_Ctypes_intsize fuel) arg1) (← (dec_Ctypes_signedness fuel) arg2) (← (dec_Ctypes_attr fuel) arg3) (← (dec_z fuel) arg4) (← (dec_bool fuel) arg5)
    | _ => throw "invalid Ctypes_member constructor or arity"

def dec_Ctypes_composite_definition : Nat → Json → CodecResult (Cfrontend.Ctypes.composite_definition)
  | 0, _ => throw "interchange depth exceeded"
  | fuel + 1, value => do
    match ← fields value with
    | [.str "Composite", arg0, arg1, arg2, arg3] =>
      return .Composite (← (dec_pos fuel) arg0) (← (dec_Ctypes_struct_or_union fuel) arg1) (← (decList (dec_Ctypes_member fuel)) arg2) (← (dec_Ctypes_attr fuel) arg3)
    | _ => throw "invalid Ctypes_composite_definition constructor or arity"

def dec_Ctypes_bitfield : Nat → Json → CodecResult (Cfrontend.Ctypes.bitfield)
  | 0, _ => throw "interchange depth exceeded"
  | fuel + 1, value => do
    match ← fields value with
    | [.str "Full"] =>
      return .Full
    | [.str "Bits", arg0, arg1, arg2, arg3] =>
      return .Bits (← (dec_Ctypes_intsize fuel) arg0) (← (dec_Ctypes_signedness fuel) arg1) (← (dec_z fuel) arg2) (← (dec_z fuel) arg3)
    | _ => throw "invalid Ctypes_bitfield constructor or arity"

def dec_Cop_unary_operation : Nat → Json → CodecResult (Cfrontend.Cop.unary_operation)
  | 0, _ => throw "interchange depth exceeded"
  | fuel + 1, value => do
    match ← fields value with
    | [.str "Onotbool"] =>
      return .Onotbool
    | [.str "Onotint"] =>
      return .Onotint
    | [.str "Oneg"] =>
      return .Oneg
    | [.str "Oabsfloat"] =>
      return .Oabsfloat
    | _ => throw "invalid Cop_unary_operation constructor or arity"

def dec_Cop_binary_operation : Nat → Json → CodecResult (Cfrontend.Cop.binary_operation)
  | 0, _ => throw "interchange depth exceeded"
  | fuel + 1, value => do
    match ← fields value with
    | [.str "Oadd"] =>
      return .Oadd
    | [.str "Osub"] =>
      return .Osub
    | [.str "Omul"] =>
      return .Omul
    | [.str "Odiv"] =>
      return .Odiv
    | [.str "Omod"] =>
      return .Omod
    | [.str "Oand"] =>
      return .Oand
    | [.str "Oor"] =>
      return .Oor
    | [.str "Oxor"] =>
      return .Oxor
    | [.str "Oshl"] =>
      return .Oshl
    | [.str "Oshr"] =>
      return .Oshr
    | [.str "Oeq"] =>
      return .Oeq
    | [.str "One"] =>
      return .One
    | [.str "Olt"] =>
      return .Olt
    | [.str "Ogt"] =>
      return .Ogt
    | [.str "Ole"] =>
      return .Ole
    | [.str "Oge"] =>
      return .Oge
    | _ => throw "invalid Cop_binary_operation constructor or arity"

def dec_Cop_incr_or_decr : Nat → Json → CodecResult (Cfrontend.Cop.incr_or_decr)
  | 0, _ => throw "interchange depth exceeded"
  | fuel + 1, value => do
    match ← fields value with
    | [.str "Incr"] =>
      return .Incr
    | [.str "Decr"] =>
      return .Decr
    | _ => throw "invalid Cop_incr_or_decr constructor or arity"

def dec_Values_coq_val : Nat → Json → CodecResult (Common.Values.val)
  | 0, _ => throw "interchange depth exceeded"
  | fuel + 1, value => do
    match ← fields value with
    | [.str "Vundef"] =>
      return .Vundef
    | [.str "Vint", arg0] =>
      return .Vint (← (dec_int fuel) arg0)
    | [.str "Vlong", arg0] =>
      return .Vlong (← (dec_long fuel) arg0)
    | [.str "Vfloat", arg0] =>
      return .Vfloat (← (dec_float fuel) arg0)
    | [.str "Vsingle", arg0] =>
      return .Vsingle (← (dec_single fuel) arg0)
    | [.str "Vptr", arg0, arg1] =>
      return .Vptr (← (dec_pos fuel) arg0) (← (dec_ptr fuel) arg1)
    | _ => throw "invalid Values_coq_val constructor or arity"

def dec_Csyntax_expr : Nat → Json → CodecResult (Cfrontend.Csyntax.expr)
  | 0, _ => throw "interchange depth exceeded"
  | fuel + 1, value => do
    match ← fields value with
    | [.str "Eval", arg0, arg1] =>
      return .Eval (← (dec_Values_coq_val fuel) arg0) (← (dec_Ctypes_coq_type fuel) arg1)
    | [.str "Evar", arg0, arg1] =>
      return .Evar (← (dec_pos fuel) arg0) (← (dec_Ctypes_coq_type fuel) arg1)
    | [.str "Efield", arg0, arg1, arg2] =>
      return .Efield (← (dec_Csyntax_expr fuel) arg0) (← (dec_pos fuel) arg1) (← (dec_Ctypes_coq_type fuel) arg2)
    | [.str "Evalof", arg0, arg1] =>
      return .Evalof (← (dec_Csyntax_expr fuel) arg0) (← (dec_Ctypes_coq_type fuel) arg1)
    | [.str "Ederef", arg0, arg1] =>
      return .Ederef (← (dec_Csyntax_expr fuel) arg0) (← (dec_Ctypes_coq_type fuel) arg1)
    | [.str "Eaddrof", arg0, arg1] =>
      return .Eaddrof (← (dec_Csyntax_expr fuel) arg0) (← (dec_Ctypes_coq_type fuel) arg1)
    | [.str "Eunop", arg0, arg1, arg2] =>
      return .Eunop (← (dec_Cop_unary_operation fuel) arg0) (← (dec_Csyntax_expr fuel) arg1) (← (dec_Ctypes_coq_type fuel) arg2)
    | [.str "Ebinop", arg0, arg1, arg2, arg3] =>
      return .Ebinop (← (dec_Cop_binary_operation fuel) arg0) (← (dec_Csyntax_expr fuel) arg1) (← (dec_Csyntax_expr fuel) arg2) (← (dec_Ctypes_coq_type fuel) arg3)
    | [.str "Ecast", arg0, arg1] =>
      return .Ecast (← (dec_Csyntax_expr fuel) arg0) (← (dec_Ctypes_coq_type fuel) arg1)
    | [.str "Eseqand", arg0, arg1, arg2] =>
      return .Eseqand (← (dec_Csyntax_expr fuel) arg0) (← (dec_Csyntax_expr fuel) arg1) (← (dec_Ctypes_coq_type fuel) arg2)
    | [.str "Eseqor", arg0, arg1, arg2] =>
      return .Eseqor (← (dec_Csyntax_expr fuel) arg0) (← (dec_Csyntax_expr fuel) arg1) (← (dec_Ctypes_coq_type fuel) arg2)
    | [.str "Econdition", arg0, arg1, arg2, arg3] =>
      return .Econdition (← (dec_Csyntax_expr fuel) arg0) (← (dec_Csyntax_expr fuel) arg1) (← (dec_Csyntax_expr fuel) arg2) (← (dec_Ctypes_coq_type fuel) arg3)
    | [.str "Esizeof", arg0, arg1] =>
      return .Esizeof (← (dec_Ctypes_coq_type fuel) arg0) (← (dec_Ctypes_coq_type fuel) arg1)
    | [.str "Ealignof", arg0, arg1] =>
      return .Ealignof (← (dec_Ctypes_coq_type fuel) arg0) (← (dec_Ctypes_coq_type fuel) arg1)
    | [.str "Eassign", arg0, arg1, arg2] =>
      return .Eassign (← (dec_Csyntax_expr fuel) arg0) (← (dec_Csyntax_expr fuel) arg1) (← (dec_Ctypes_coq_type fuel) arg2)
    | [.str "Eassignop", arg0, arg1, arg2, arg3, arg4] =>
      return .Eassignop (← (dec_Cop_binary_operation fuel) arg0) (← (dec_Csyntax_expr fuel) arg1) (← (dec_Csyntax_expr fuel) arg2) (← (dec_Ctypes_coq_type fuel) arg3) (← (dec_Ctypes_coq_type fuel) arg4)
    | [.str "Epostincr", arg0, arg1, arg2] =>
      return .Epostincr (← (dec_Cop_incr_or_decr fuel) arg0) (← (dec_Csyntax_expr fuel) arg1) (← (dec_Ctypes_coq_type fuel) arg2)
    | [.str "Ecomma", arg0, arg1, arg2] =>
      return .Ecomma (← (dec_Csyntax_expr fuel) arg0) (← (dec_Csyntax_expr fuel) arg1) (← (dec_Ctypes_coq_type fuel) arg2)
    | [.str "Ecall", arg0, arg1, arg2] =>
      return .Ecall (← (dec_Csyntax_expr fuel) arg0) (← (dec_Csyntax_exprlist fuel) arg1) (← (dec_Ctypes_coq_type fuel) arg2)
    | [.str "Ebuiltin", arg0, arg1, arg2, arg3] =>
      return .Ebuiltin (← (dec_AST_external_function fuel) arg0) (← (decList (dec_Ctypes_coq_type fuel)) arg1) (← (dec_Csyntax_exprlist fuel) arg2) (← (dec_Ctypes_coq_type fuel) arg3)
    | [.str "Eloc", arg0, arg1, arg2, arg3] =>
      return .Eloc (← (dec_pos fuel) arg0) (← (dec_ptr fuel) arg1) (← (dec_Ctypes_bitfield fuel) arg2) (← (dec_Ctypes_coq_type fuel) arg3)
    | [.str "Eparen", arg0, arg1, arg2] =>
      return .Eparen (← (dec_Csyntax_expr fuel) arg0) (← (dec_Ctypes_coq_type fuel) arg1) (← (dec_Ctypes_coq_type fuel) arg2)
    | _ => throw "invalid Csyntax_expr constructor or arity"

def dec_Csyntax_exprlist : Nat → Json → CodecResult (Cfrontend.Csyntax.exprlist)
  | 0, _ => throw "interchange depth exceeded"
  | fuel + 1, value => do
    match ← fields value with
    | [.str "Enil"] =>
      return .Enil
    | [.str "Econs", arg0, arg1] =>
      return .Econs (← (dec_Csyntax_expr fuel) arg0) (← (dec_Csyntax_exprlist fuel) arg1)
    | _ => throw "invalid Csyntax_exprlist constructor or arity"

def dec_Csyntax_statement : Nat → Json → CodecResult (Cfrontend.Csyntax.statement)
  | 0, _ => throw "interchange depth exceeded"
  | fuel + 1, value => do
    match ← fields value with
    | [.str "Sskip"] =>
      return .Sskip
    | [.str "Sdo", arg0] =>
      return .Sdo (← (dec_Csyntax_expr fuel) arg0)
    | [.str "Ssequence", arg0, arg1] =>
      return .Ssequence (← (dec_Csyntax_statement fuel) arg0) (← (dec_Csyntax_statement fuel) arg1)
    | [.str "Sifthenelse", arg0, arg1, arg2] =>
      return .Sifthenelse (← (dec_Csyntax_expr fuel) arg0) (← (dec_Csyntax_statement fuel) arg1) (← (dec_Csyntax_statement fuel) arg2)
    | [.str "Swhile", arg0, arg1] =>
      return .Swhile (← (dec_Csyntax_expr fuel) arg0) (← (dec_Csyntax_statement fuel) arg1)
    | [.str "Sdowhile", arg0, arg1] =>
      return .Sdowhile (← (dec_Csyntax_expr fuel) arg0) (← (dec_Csyntax_statement fuel) arg1)
    | [.str "Sfor", arg0, arg1, arg2, arg3] =>
      return .Sfor (← (dec_Csyntax_statement fuel) arg0) (← (dec_Csyntax_expr fuel) arg1) (← (dec_Csyntax_statement fuel) arg2) (← (dec_Csyntax_statement fuel) arg3)
    | [.str "Sbreak"] =>
      return .Sbreak
    | [.str "Scontinue"] =>
      return .Scontinue
    | [.str "Sreturn", arg0] =>
      return .Sreturn (← (decOption (dec_Csyntax_expr fuel)) arg0)
    | [.str "Sswitch", arg0, arg1] =>
      return .Sswitch (← (dec_Csyntax_expr fuel) arg0) (← (dec_Csyntax_labeled_statements fuel) arg1)
    | [.str "Slabel", arg0, arg1] =>
      return .Slabel (← (dec_pos fuel) arg0) (← (dec_Csyntax_statement fuel) arg1)
    | [.str "Sgoto", arg0] =>
      return .Sgoto (← (dec_pos fuel) arg0)
    | _ => throw "invalid Csyntax_statement constructor or arity"

def dec_Csyntax_labeled_statements : Nat → Json → CodecResult (Cfrontend.Csyntax.labeled_statements)
  | 0, _ => throw "interchange depth exceeded"
  | fuel + 1, value => do
    match ← fields value with
    | [.str "LSnil"] =>
      return .LSnil
    | [.str "LScons", arg0, arg1, arg2] =>
      return .LScons (← (decOption (dec_z fuel)) arg0) (← (dec_Csyntax_statement fuel) arg1) (← (dec_Csyntax_labeled_statements fuel) arg2)
    | _ => throw "invalid Csyntax_labeled_statements constructor or arity"

def dec_Csyntax_coq_function : Nat → Json → CodecResult (Cfrontend.Csyntax.function)
  | 0, _ => throw "interchange depth exceeded"
  | fuel + 1, value => do
    match ← fields value with
    | [.str "Csyntax_coq_function", arg0, arg1, arg2, arg3, arg4] =>
      return { fn_return := (← (dec_Ctypes_coq_type fuel) arg0), fn_callconv := (← (dec_AST_calling_convention fuel) arg1), fn_params := (← (decList (decPair (dec_pos fuel) (dec_Ctypes_coq_type fuel))) arg2), fn_vars := (← (decList (decPair (dec_pos fuel) (dec_Ctypes_coq_type fuel))) arg3), fn_body := (← (dec_Csyntax_statement fuel) arg4) }
    | _ => throw "invalid Csyntax_coq_function constructor or arity"

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
    match ← fields value with
    | [.str "Internal", arg0] =>
      return .Internal (← (dec_Csyntax_coq_function fuel) arg0)
    | [.str "External", arg0, arg1, arg2, arg3] =>
      return .External (← (dec_AST_external_function fuel) arg0) (← (decList (dec_Ctypes_coq_type fuel)) arg1) (← (dec_Ctypes_coq_type fuel) arg2) (← (dec_AST_calling_convention fuel) arg3)
    | _ => throw "invalid CFundef constructor or arity"

def dec_CGlobvar : Nat → Json → CodecResult (Common.AST.globvar (Cfrontend.Ctypes.type))
  | 0, _ => throw "interchange depth exceeded"
  | fuel + 1, value => do
    match ← fields value with
    | [.str "CGlobvar", arg0, arg1, arg2, arg3] =>
      return { gvar_info := (← (dec_Ctypes_coq_type fuel) arg0), gvar_init := (← (decList (dec_AST_init_data fuel)) arg1), gvar_readonly := (← (dec_bool fuel) arg2), gvar_volatile := (← (dec_bool fuel) arg3) }
    | _ => throw "invalid CGlobvar constructor or arity"

def dec_CGlobdef : Nat → Json → CodecResult (Common.AST.globdef (Cfrontend.Ctypes.fundef (Cfrontend.Csyntax.function)) (Cfrontend.Ctypes.type))
  | 0, _ => throw "interchange depth exceeded"
  | fuel + 1, value => do
    match ← fields value with
    | [.str "Gfun", arg0] =>
      return .Gfun (← (dec_CFundef fuel) arg0)
    | [.str "Gvar", arg0] =>
      return .Gvar (← (dec_CGlobvar fuel) arg0)
    | _ => throw "invalid CGlobdef constructor or arity"

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
end CodecReference

theorem indexed_decoders_eq (fuel : Nat) :
    CompCert4Lean.Prototype.dec_AST_typ fuel = CodecReference.dec_AST_typ fuel ∧
    CompCert4Lean.Prototype.dec_AST_xtype fuel = CodecReference.dec_AST_xtype fuel ∧
    CompCert4Lean.Prototype.dec_AST_calling_convention fuel = CodecReference.dec_AST_calling_convention fuel ∧
    CompCert4Lean.Prototype.dec_AST_signature fuel = CodecReference.dec_AST_signature fuel ∧
    CompCert4Lean.Prototype.dec_AST_memory_chunk fuel = CodecReference.dec_AST_memory_chunk fuel ∧
    CompCert4Lean.Prototype.dec_AST_init_data fuel = CodecReference.dec_AST_init_data fuel ∧
    CompCert4Lean.Prototype.dec_AST_external_function fuel = CodecReference.dec_AST_external_function fuel ∧
    CompCert4Lean.Prototype.dec_Ctypes_signedness fuel = CodecReference.dec_Ctypes_signedness fuel ∧
    CompCert4Lean.Prototype.dec_Ctypes_intsize fuel = CodecReference.dec_Ctypes_intsize fuel ∧
    CompCert4Lean.Prototype.dec_Ctypes_floatsize fuel = CodecReference.dec_Ctypes_floatsize fuel ∧
    CompCert4Lean.Prototype.dec_Ctypes_attr fuel = CodecReference.dec_Ctypes_attr fuel ∧
    CompCert4Lean.Prototype.dec_Ctypes_coq_type fuel = CodecReference.dec_Ctypes_coq_type fuel ∧
    CompCert4Lean.Prototype.dec_Ctypes_struct_or_union fuel = CodecReference.dec_Ctypes_struct_or_union fuel ∧
    CompCert4Lean.Prototype.dec_Ctypes_member fuel = CodecReference.dec_Ctypes_member fuel ∧
    CompCert4Lean.Prototype.dec_Ctypes_composite_definition fuel = CodecReference.dec_Ctypes_composite_definition fuel ∧
    CompCert4Lean.Prototype.dec_Ctypes_bitfield fuel = CodecReference.dec_Ctypes_bitfield fuel ∧
    CompCert4Lean.Prototype.dec_Cop_unary_operation fuel = CodecReference.dec_Cop_unary_operation fuel ∧
    CompCert4Lean.Prototype.dec_Cop_binary_operation fuel = CodecReference.dec_Cop_binary_operation fuel ∧
    CompCert4Lean.Prototype.dec_Cop_incr_or_decr fuel = CodecReference.dec_Cop_incr_or_decr fuel ∧
    CompCert4Lean.Prototype.dec_Values_coq_val fuel = CodecReference.dec_Values_coq_val fuel ∧
    CompCert4Lean.Prototype.dec_Csyntax_expr fuel = CodecReference.dec_Csyntax_expr fuel ∧
    CompCert4Lean.Prototype.dec_Csyntax_exprlist fuel = CodecReference.dec_Csyntax_exprlist fuel ∧
    CompCert4Lean.Prototype.dec_Csyntax_statement fuel = CodecReference.dec_Csyntax_statement fuel ∧
    CompCert4Lean.Prototype.dec_Csyntax_labeled_statements fuel = CodecReference.dec_Csyntax_labeled_statements fuel ∧
    CompCert4Lean.Prototype.dec_Csyntax_coq_function fuel = CodecReference.dec_Csyntax_coq_function fuel ∧
    CompCert4Lean.Prototype.dec_CFundef fuel = CodecReference.dec_CFundef fuel ∧
    CompCert4Lean.Prototype.dec_CGlobvar fuel = CodecReference.dec_CGlobvar fuel ∧
    CompCert4Lean.Prototype.dec_CGlobdef fuel = CodecReference.dec_CGlobdef fuel := by
  induction fuel with
  | zero =>
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
  | succ fuel previous =>
    rcases previous with ⟨previous_dec_AST_typ, previous_dec_AST_xtype, previous_dec_AST_calling_convention, previous_dec_AST_signature, previous_dec_AST_memory_chunk, previous_dec_AST_init_data, previous_dec_AST_external_function, previous_dec_Ctypes_signedness, previous_dec_Ctypes_intsize, previous_dec_Ctypes_floatsize, previous_dec_Ctypes_attr, previous_dec_Ctypes_coq_type, previous_dec_Ctypes_struct_or_union, previous_dec_Ctypes_member, previous_dec_Ctypes_composite_definition, previous_dec_Ctypes_bitfield, previous_dec_Cop_unary_operation, previous_dec_Cop_binary_operation, previous_dec_Cop_incr_or_decr, previous_dec_Values_coq_val, previous_dec_Csyntax_expr, previous_dec_Csyntax_exprlist, previous_dec_Csyntax_statement, previous_dec_Csyntax_labeled_statements, previous_dec_Csyntax_coq_function, previous_dec_CFundef, previous_dec_CGlobvar, previous_dec_CGlobdef⟩
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · funext value
      cases value with
      | arr values =>
        rcases values with ⟨values⟩
        cases values with
        | nil =>
          simp [CompCert4Lean.Prototype.dec_AST_typ, CodecReference.dec_AST_typ, fields, Json.getArr?, previous_dec_AST_typ]
        | cons head0 tail1 =>
          cases tail1 with
          | nil =>
            cases head0 <;> simp [CompCert4Lean.Prototype.dec_AST_typ, CodecReference.dec_AST_typ, fields, Json.getArr?, previous_dec_AST_typ]
            all_goals split <;> simp_all
          | cons head1 tail2 =>
            have wrong1 : (Array.mk (head0 :: head1 :: tail2)).size ≠ 1 := by
              change tail2.length + 2 ≠ 1
              omega
            simp [CompCert4Lean.Prototype.dec_AST_typ, CodecReference.dec_AST_typ, fields, Json.getArr?, previous_dec_AST_typ, wrong1]
      | _ => rfl
    · funext value
      cases value with
      | arr values =>
        rcases values with ⟨values⟩
        cases values with
        | nil =>
          simp [CompCert4Lean.Prototype.dec_AST_xtype, CodecReference.dec_AST_xtype, fields, Json.getArr?, previous_dec_AST_xtype]
        | cons head0 tail1 =>
          cases tail1 with
          | nil =>
            cases head0 <;> simp [CompCert4Lean.Prototype.dec_AST_xtype, CodecReference.dec_AST_xtype, fields, Json.getArr?, previous_dec_AST_xtype]
            all_goals split <;> simp_all
          | cons head1 tail2 =>
            have wrong1 : (Array.mk (head0 :: head1 :: tail2)).size ≠ 1 := by
              change tail2.length + 2 ≠ 1
              omega
            simp [CompCert4Lean.Prototype.dec_AST_xtype, CodecReference.dec_AST_xtype, fields, Json.getArr?, previous_dec_AST_xtype, wrong1]
      | _ => rfl
    · funext value
      cases value with
      | arr values =>
        rcases values with ⟨values⟩
        cases values with
        | nil =>
          simp [CompCert4Lean.Prototype.dec_AST_calling_convention, CodecReference.dec_AST_calling_convention, fields, Json.getArr?, previous_dec_AST_calling_convention]
        | cons head0 tail1 =>
          cases tail1 with
          | nil =>
            cases head0 <;> simp [CompCert4Lean.Prototype.dec_AST_calling_convention, CodecReference.dec_AST_calling_convention, fields, Json.getArr?, previous_dec_AST_calling_convention]
            all_goals split <;> simp_all
          | cons head1 tail2 =>
            cases tail2 with
            | nil =>
              cases head0 <;> simp [CompCert4Lean.Prototype.dec_AST_calling_convention, CodecReference.dec_AST_calling_convention, fields, Json.getArr?, previous_dec_AST_calling_convention]
              all_goals split <;> simp_all
            | cons head2 tail3 =>
              cases tail3 with
              | nil =>
                cases head0 <;> simp [CompCert4Lean.Prototype.dec_AST_calling_convention, CodecReference.dec_AST_calling_convention, fields, Json.getArr?, previous_dec_AST_calling_convention]
                all_goals split <;> simp_all
              | cons head3 tail4 =>
                cases tail4 with
                | nil =>
                  cases head0 <;> simp [CompCert4Lean.Prototype.dec_AST_calling_convention, CodecReference.dec_AST_calling_convention, fields, Json.getArr?, previous_dec_AST_calling_convention]
                  all_goals split <;> simp_all
                | cons head4 tail5 =>
                  have wrong4 : (Array.mk (head0 :: head1 :: head2 :: head3 :: head4 :: tail5)).size ≠ 4 := by
                    change tail5.length + 5 ≠ 4
                    omega
                  simp [CompCert4Lean.Prototype.dec_AST_calling_convention, CodecReference.dec_AST_calling_convention, fields, Json.getArr?, previous_dec_AST_calling_convention, wrong4]
      | _ => rfl
    · funext value
      cases value with
      | arr values =>
        rcases values with ⟨values⟩
        cases values with
        | nil =>
          simp [CompCert4Lean.Prototype.dec_AST_signature, CodecReference.dec_AST_signature, fields, Json.getArr?, previous_dec_AST_xtype, previous_dec_AST_calling_convention, previous_dec_AST_signature]
        | cons head0 tail1 =>
          cases tail1 with
          | nil =>
            cases head0 <;> simp [CompCert4Lean.Prototype.dec_AST_signature, CodecReference.dec_AST_signature, fields, Json.getArr?, previous_dec_AST_xtype, previous_dec_AST_calling_convention, previous_dec_AST_signature]
            all_goals split <;> simp_all
          | cons head1 tail2 =>
            cases tail2 with
            | nil =>
              cases head0 <;> simp [CompCert4Lean.Prototype.dec_AST_signature, CodecReference.dec_AST_signature, fields, Json.getArr?, previous_dec_AST_xtype, previous_dec_AST_calling_convention, previous_dec_AST_signature]
              all_goals split <;> simp_all
            | cons head2 tail3 =>
              cases tail3 with
              | nil =>
                cases head0 <;> simp [CompCert4Lean.Prototype.dec_AST_signature, CodecReference.dec_AST_signature, fields, Json.getArr?, previous_dec_AST_xtype, previous_dec_AST_calling_convention, previous_dec_AST_signature]
                all_goals split <;> simp_all
              | cons head3 tail4 =>
                cases tail4 with
                | nil =>
                  cases head0 <;> simp [CompCert4Lean.Prototype.dec_AST_signature, CodecReference.dec_AST_signature, fields, Json.getArr?, previous_dec_AST_xtype, previous_dec_AST_calling_convention, previous_dec_AST_signature]
                  all_goals split <;> simp_all
                | cons head4 tail5 =>
                  have wrong4 : (Array.mk (head0 :: head1 :: head2 :: head3 :: head4 :: tail5)).size ≠ 4 := by
                    change tail5.length + 5 ≠ 4
                    omega
                  simp [CompCert4Lean.Prototype.dec_AST_signature, CodecReference.dec_AST_signature, fields, Json.getArr?, previous_dec_AST_xtype, previous_dec_AST_calling_convention, previous_dec_AST_signature, wrong4]
      | _ => rfl
    · funext value
      cases value with
      | arr values =>
        rcases values with ⟨values⟩
        cases values with
        | nil =>
          simp [CompCert4Lean.Prototype.dec_AST_memory_chunk, CodecReference.dec_AST_memory_chunk, fields, Json.getArr?, previous_dec_AST_memory_chunk]
        | cons head0 tail1 =>
          cases tail1 with
          | nil =>
            cases head0 <;> simp [CompCert4Lean.Prototype.dec_AST_memory_chunk, CodecReference.dec_AST_memory_chunk, fields, Json.getArr?, previous_dec_AST_memory_chunk]
            all_goals split <;> simp_all
          | cons head1 tail2 =>
            have wrong1 : (Array.mk (head0 :: head1 :: tail2)).size ≠ 1 := by
              change tail2.length + 2 ≠ 1
              omega
            simp [CompCert4Lean.Prototype.dec_AST_memory_chunk, CodecReference.dec_AST_memory_chunk, fields, Json.getArr?, previous_dec_AST_memory_chunk, wrong1]
      | _ => rfl
    · funext value
      cases value with
      | arr values =>
        rcases values with ⟨values⟩
        cases values with
        | nil =>
          simp [CompCert4Lean.Prototype.dec_AST_init_data, CodecReference.dec_AST_init_data, fields, Json.getArr?, previous_dec_AST_init_data]
        | cons head0 tail1 =>
          cases tail1 with
          | nil =>
            cases head0 <;> simp [CompCert4Lean.Prototype.dec_AST_init_data, CodecReference.dec_AST_init_data, fields, Json.getArr?, previous_dec_AST_init_data]
            all_goals split <;> simp_all
          | cons head1 tail2 =>
            cases tail2 with
            | nil =>
              cases head0 <;> simp [CompCert4Lean.Prototype.dec_AST_init_data, CodecReference.dec_AST_init_data, fields, Json.getArr?, previous_dec_AST_init_data]
              all_goals split <;> simp_all
            | cons head2 tail3 =>
              cases tail3 with
              | nil =>
                cases head0 <;> simp [CompCert4Lean.Prototype.dec_AST_init_data, CodecReference.dec_AST_init_data, fields, Json.getArr?, previous_dec_AST_init_data]
                all_goals split <;> simp_all
              | cons head3 tail4 =>
                have wrong2 : (Array.mk (head0 :: head1 :: head2 :: head3 :: tail4)).size ≠ 2 := by
                  change tail4.length + 4 ≠ 2
                  omega
                have wrong3 : (Array.mk (head0 :: head1 :: head2 :: head3 :: tail4)).size ≠ 3 := by
                  change tail4.length + 4 ≠ 3
                  omega
                simp [CompCert4Lean.Prototype.dec_AST_init_data, CodecReference.dec_AST_init_data, fields, Json.getArr?, previous_dec_AST_init_data, wrong2, wrong3]
      | _ => rfl
    · funext value
      cases value with
      | arr values =>
        rcases values with ⟨values⟩
        cases values with
        | nil =>
          simp [CompCert4Lean.Prototype.dec_AST_external_function, CodecReference.dec_AST_external_function, fields, Json.getArr?, previous_dec_AST_typ, previous_dec_AST_signature, previous_dec_AST_memory_chunk, previous_dec_AST_external_function]
        | cons head0 tail1 =>
          cases tail1 with
          | nil =>
            cases head0 <;> simp [CompCert4Lean.Prototype.dec_AST_external_function, CodecReference.dec_AST_external_function, fields, Json.getArr?, previous_dec_AST_typ, previous_dec_AST_signature, previous_dec_AST_memory_chunk, previous_dec_AST_external_function]
            all_goals split <;> simp_all
          | cons head1 tail2 =>
            cases tail2 with
            | nil =>
              cases head0 <;> simp [CompCert4Lean.Prototype.dec_AST_external_function, CodecReference.dec_AST_external_function, fields, Json.getArr?, previous_dec_AST_typ, previous_dec_AST_signature, previous_dec_AST_memory_chunk, previous_dec_AST_external_function]
              all_goals split <;> simp_all
            | cons head2 tail3 =>
              cases tail3 with
              | nil =>
                cases head0 <;> simp [CompCert4Lean.Prototype.dec_AST_external_function, CodecReference.dec_AST_external_function, fields, Json.getArr?, previous_dec_AST_typ, previous_dec_AST_signature, previous_dec_AST_memory_chunk, previous_dec_AST_external_function]
                all_goals split <;> simp_all
              | cons head3 tail4 =>
                cases tail4 with
                | nil =>
                  cases head0 <;> simp [CompCert4Lean.Prototype.dec_AST_external_function, CodecReference.dec_AST_external_function, fields, Json.getArr?, previous_dec_AST_typ, previous_dec_AST_signature, previous_dec_AST_memory_chunk, previous_dec_AST_external_function]
                  all_goals split <;> simp_all
                | cons head4 tail5 =>
                  have wrong1 : (Array.mk (head0 :: head1 :: head2 :: head3 :: head4 :: tail5)).size ≠ 1 := by
                    change tail5.length + 5 ≠ 1
                    omega
                  have wrong2 : (Array.mk (head0 :: head1 :: head2 :: head3 :: head4 :: tail5)).size ≠ 2 := by
                    change tail5.length + 5 ≠ 2
                    omega
                  have wrong3 : (Array.mk (head0 :: head1 :: head2 :: head3 :: head4 :: tail5)).size ≠ 3 := by
                    change tail5.length + 5 ≠ 3
                    omega
                  have wrong4 : (Array.mk (head0 :: head1 :: head2 :: head3 :: head4 :: tail5)).size ≠ 4 := by
                    change tail5.length + 5 ≠ 4
                    omega
                  simp [CompCert4Lean.Prototype.dec_AST_external_function, CodecReference.dec_AST_external_function, fields, Json.getArr?, previous_dec_AST_typ, previous_dec_AST_signature, previous_dec_AST_memory_chunk, previous_dec_AST_external_function, wrong1, wrong2, wrong3, wrong4]
      | _ => rfl
    · funext value
      cases value with
      | arr values =>
        rcases values with ⟨values⟩
        cases values with
        | nil =>
          simp [CompCert4Lean.Prototype.dec_Ctypes_signedness, CodecReference.dec_Ctypes_signedness, fields, Json.getArr?, previous_dec_Ctypes_signedness]
        | cons head0 tail1 =>
          cases tail1 with
          | nil =>
            cases head0 <;> simp [CompCert4Lean.Prototype.dec_Ctypes_signedness, CodecReference.dec_Ctypes_signedness, fields, Json.getArr?, previous_dec_Ctypes_signedness]
            all_goals split <;> simp_all
          | cons head1 tail2 =>
            have wrong1 : (Array.mk (head0 :: head1 :: tail2)).size ≠ 1 := by
              change tail2.length + 2 ≠ 1
              omega
            simp [CompCert4Lean.Prototype.dec_Ctypes_signedness, CodecReference.dec_Ctypes_signedness, fields, Json.getArr?, previous_dec_Ctypes_signedness, wrong1]
      | _ => rfl
    · funext value
      cases value with
      | arr values =>
        rcases values with ⟨values⟩
        cases values with
        | nil =>
          simp [CompCert4Lean.Prototype.dec_Ctypes_intsize, CodecReference.dec_Ctypes_intsize, fields, Json.getArr?, previous_dec_Ctypes_intsize]
        | cons head0 tail1 =>
          cases tail1 with
          | nil =>
            cases head0 <;> simp [CompCert4Lean.Prototype.dec_Ctypes_intsize, CodecReference.dec_Ctypes_intsize, fields, Json.getArr?, previous_dec_Ctypes_intsize]
            all_goals split <;> simp_all
          | cons head1 tail2 =>
            have wrong1 : (Array.mk (head0 :: head1 :: tail2)).size ≠ 1 := by
              change tail2.length + 2 ≠ 1
              omega
            simp [CompCert4Lean.Prototype.dec_Ctypes_intsize, CodecReference.dec_Ctypes_intsize, fields, Json.getArr?, previous_dec_Ctypes_intsize, wrong1]
      | _ => rfl
    · funext value
      cases value with
      | arr values =>
        rcases values with ⟨values⟩
        cases values with
        | nil =>
          simp [CompCert4Lean.Prototype.dec_Ctypes_floatsize, CodecReference.dec_Ctypes_floatsize, fields, Json.getArr?, previous_dec_Ctypes_floatsize]
        | cons head0 tail1 =>
          cases tail1 with
          | nil =>
            cases head0 <;> simp [CompCert4Lean.Prototype.dec_Ctypes_floatsize, CodecReference.dec_Ctypes_floatsize, fields, Json.getArr?, previous_dec_Ctypes_floatsize]
            all_goals split <;> simp_all
          | cons head1 tail2 =>
            have wrong1 : (Array.mk (head0 :: head1 :: tail2)).size ≠ 1 := by
              change tail2.length + 2 ≠ 1
              omega
            simp [CompCert4Lean.Prototype.dec_Ctypes_floatsize, CodecReference.dec_Ctypes_floatsize, fields, Json.getArr?, previous_dec_Ctypes_floatsize, wrong1]
      | _ => rfl
    · funext value
      cases value with
      | arr values =>
        rcases values with ⟨values⟩
        cases values with
        | nil =>
          simp [CompCert4Lean.Prototype.dec_Ctypes_attr, CodecReference.dec_Ctypes_attr, fields, Json.getArr?, previous_dec_Ctypes_attr]
        | cons head0 tail1 =>
          cases tail1 with
          | nil =>
            cases head0 <;> simp [CompCert4Lean.Prototype.dec_Ctypes_attr, CodecReference.dec_Ctypes_attr, fields, Json.getArr?, previous_dec_Ctypes_attr]
            all_goals split <;> simp_all
          | cons head1 tail2 =>
            cases tail2 with
            | nil =>
              cases head0 <;> simp [CompCert4Lean.Prototype.dec_Ctypes_attr, CodecReference.dec_Ctypes_attr, fields, Json.getArr?, previous_dec_Ctypes_attr]
              all_goals split <;> simp_all
            | cons head2 tail3 =>
              cases tail3 with
              | nil =>
                cases head0 <;> simp [CompCert4Lean.Prototype.dec_Ctypes_attr, CodecReference.dec_Ctypes_attr, fields, Json.getArr?, previous_dec_Ctypes_attr]
                all_goals split <;> simp_all
              | cons head3 tail4 =>
                have wrong3 : (Array.mk (head0 :: head1 :: head2 :: head3 :: tail4)).size ≠ 3 := by
                  change tail4.length + 4 ≠ 3
                  omega
                simp [CompCert4Lean.Prototype.dec_Ctypes_attr, CodecReference.dec_Ctypes_attr, fields, Json.getArr?, previous_dec_Ctypes_attr, wrong3]
      | _ => rfl
    · funext value
      cases value with
      | arr values =>
        rcases values with ⟨values⟩
        cases values with
        | nil =>
          simp [CompCert4Lean.Prototype.dec_Ctypes_coq_type, CodecReference.dec_Ctypes_coq_type, fields, Json.getArr?, previous_dec_AST_calling_convention, previous_dec_Ctypes_signedness, previous_dec_Ctypes_intsize, previous_dec_Ctypes_floatsize, previous_dec_Ctypes_attr, previous_dec_Ctypes_coq_type]
        | cons head0 tail1 =>
          cases tail1 with
          | nil =>
            cases head0 <;> simp [CompCert4Lean.Prototype.dec_Ctypes_coq_type, CodecReference.dec_Ctypes_coq_type, fields, Json.getArr?, previous_dec_AST_calling_convention, previous_dec_Ctypes_signedness, previous_dec_Ctypes_intsize, previous_dec_Ctypes_floatsize, previous_dec_Ctypes_attr, previous_dec_Ctypes_coq_type]
            all_goals split <;> simp_all
          | cons head1 tail2 =>
            cases tail2 with
            | nil =>
              cases head0 <;> simp [CompCert4Lean.Prototype.dec_Ctypes_coq_type, CodecReference.dec_Ctypes_coq_type, fields, Json.getArr?, previous_dec_AST_calling_convention, previous_dec_Ctypes_signedness, previous_dec_Ctypes_intsize, previous_dec_Ctypes_floatsize, previous_dec_Ctypes_attr, previous_dec_Ctypes_coq_type]
              all_goals split <;> simp_all
            | cons head2 tail3 =>
              cases tail3 with
              | nil =>
                cases head0 <;> simp [CompCert4Lean.Prototype.dec_Ctypes_coq_type, CodecReference.dec_Ctypes_coq_type, fields, Json.getArr?, previous_dec_AST_calling_convention, previous_dec_Ctypes_signedness, previous_dec_Ctypes_intsize, previous_dec_Ctypes_floatsize, previous_dec_Ctypes_attr, previous_dec_Ctypes_coq_type]
                all_goals split <;> simp_all
              | cons head3 tail4 =>
                cases tail4 with
                | nil =>
                  cases head0 <;> simp [CompCert4Lean.Prototype.dec_Ctypes_coq_type, CodecReference.dec_Ctypes_coq_type, fields, Json.getArr?, previous_dec_AST_calling_convention, previous_dec_Ctypes_signedness, previous_dec_Ctypes_intsize, previous_dec_Ctypes_floatsize, previous_dec_Ctypes_attr, previous_dec_Ctypes_coq_type]
                  all_goals split <;> simp_all
                | cons head4 tail5 =>
                  have wrong1 : (Array.mk (head0 :: head1 :: head2 :: head3 :: head4 :: tail5)).size ≠ 1 := by
                    change tail5.length + 5 ≠ 1
                    omega
                  have wrong3 : (Array.mk (head0 :: head1 :: head2 :: head3 :: head4 :: tail5)).size ≠ 3 := by
                    change tail5.length + 5 ≠ 3
                    omega
                  have wrong4 : (Array.mk (head0 :: head1 :: head2 :: head3 :: head4 :: tail5)).size ≠ 4 := by
                    change tail5.length + 5 ≠ 4
                    omega
                  simp [CompCert4Lean.Prototype.dec_Ctypes_coq_type, CodecReference.dec_Ctypes_coq_type, fields, Json.getArr?, previous_dec_AST_calling_convention, previous_dec_Ctypes_signedness, previous_dec_Ctypes_intsize, previous_dec_Ctypes_floatsize, previous_dec_Ctypes_attr, previous_dec_Ctypes_coq_type, wrong1, wrong3, wrong4]
      | _ => rfl
    · funext value
      cases value with
      | arr values =>
        rcases values with ⟨values⟩
        cases values with
        | nil =>
          simp [CompCert4Lean.Prototype.dec_Ctypes_struct_or_union, CodecReference.dec_Ctypes_struct_or_union, fields, Json.getArr?, previous_dec_Ctypes_struct_or_union]
        | cons head0 tail1 =>
          cases tail1 with
          | nil =>
            cases head0 <;> simp [CompCert4Lean.Prototype.dec_Ctypes_struct_or_union, CodecReference.dec_Ctypes_struct_or_union, fields, Json.getArr?, previous_dec_Ctypes_struct_or_union]
            all_goals split <;> simp_all
          | cons head1 tail2 =>
            have wrong1 : (Array.mk (head0 :: head1 :: tail2)).size ≠ 1 := by
              change tail2.length + 2 ≠ 1
              omega
            simp [CompCert4Lean.Prototype.dec_Ctypes_struct_or_union, CodecReference.dec_Ctypes_struct_or_union, fields, Json.getArr?, previous_dec_Ctypes_struct_or_union, wrong1]
      | _ => rfl
    · funext value
      cases value with
      | arr values =>
        rcases values with ⟨values⟩
        cases values with
        | nil =>
          simp [CompCert4Lean.Prototype.dec_Ctypes_member, CodecReference.dec_Ctypes_member, fields, Json.getArr?, previous_dec_Ctypes_signedness, previous_dec_Ctypes_intsize, previous_dec_Ctypes_attr, previous_dec_Ctypes_coq_type, previous_dec_Ctypes_member]
        | cons head0 tail1 =>
          cases tail1 with
          | nil =>
            cases head0 <;> simp [CompCert4Lean.Prototype.dec_Ctypes_member, CodecReference.dec_Ctypes_member, fields, Json.getArr?, previous_dec_Ctypes_signedness, previous_dec_Ctypes_intsize, previous_dec_Ctypes_attr, previous_dec_Ctypes_coq_type, previous_dec_Ctypes_member]
            all_goals split <;> simp_all
          | cons head1 tail2 =>
            cases tail2 with
            | nil =>
              cases head0 <;> simp [CompCert4Lean.Prototype.dec_Ctypes_member, CodecReference.dec_Ctypes_member, fields, Json.getArr?, previous_dec_Ctypes_signedness, previous_dec_Ctypes_intsize, previous_dec_Ctypes_attr, previous_dec_Ctypes_coq_type, previous_dec_Ctypes_member]
              all_goals split <;> simp_all
            | cons head2 tail3 =>
              cases tail3 with
              | nil =>
                cases head0 <;> simp [CompCert4Lean.Prototype.dec_Ctypes_member, CodecReference.dec_Ctypes_member, fields, Json.getArr?, previous_dec_Ctypes_signedness, previous_dec_Ctypes_intsize, previous_dec_Ctypes_attr, previous_dec_Ctypes_coq_type, previous_dec_Ctypes_member]
                all_goals split <;> simp_all
              | cons head3 tail4 =>
                cases tail4 with
                | nil =>
                  cases head0 <;> simp [CompCert4Lean.Prototype.dec_Ctypes_member, CodecReference.dec_Ctypes_member, fields, Json.getArr?, previous_dec_Ctypes_signedness, previous_dec_Ctypes_intsize, previous_dec_Ctypes_attr, previous_dec_Ctypes_coq_type, previous_dec_Ctypes_member]
                  all_goals split <;> simp_all
                | cons head4 tail5 =>
                  cases tail5 with
                  | nil =>
                    cases head0 <;> simp [CompCert4Lean.Prototype.dec_Ctypes_member, CodecReference.dec_Ctypes_member, fields, Json.getArr?, previous_dec_Ctypes_signedness, previous_dec_Ctypes_intsize, previous_dec_Ctypes_attr, previous_dec_Ctypes_coq_type, previous_dec_Ctypes_member]
                    all_goals split <;> simp_all
                  | cons head5 tail6 =>
                    cases tail6 with
                    | nil =>
                      cases head0 <;> simp [CompCert4Lean.Prototype.dec_Ctypes_member, CodecReference.dec_Ctypes_member, fields, Json.getArr?, previous_dec_Ctypes_signedness, previous_dec_Ctypes_intsize, previous_dec_Ctypes_attr, previous_dec_Ctypes_coq_type, previous_dec_Ctypes_member]
                      all_goals split <;> simp_all
                    | cons head6 tail7 =>
                      cases tail7 with
                      | nil =>
                        cases head0 <;> simp [CompCert4Lean.Prototype.dec_Ctypes_member, CodecReference.dec_Ctypes_member, fields, Json.getArr?, previous_dec_Ctypes_signedness, previous_dec_Ctypes_intsize, previous_dec_Ctypes_attr, previous_dec_Ctypes_coq_type, previous_dec_Ctypes_member]
                        all_goals split <;> simp_all
                      | cons head7 tail8 =>
                        have wrong3 : (Array.mk (head0 :: head1 :: head2 :: head3 :: head4 :: head5 :: head6 :: head7 :: tail8)).size ≠ 3 := by
                          change tail8.length + 8 ≠ 3
                          omega
                        have wrong7 : (Array.mk (head0 :: head1 :: head2 :: head3 :: head4 :: head5 :: head6 :: head7 :: tail8)).size ≠ 7 := by
                          change tail8.length + 8 ≠ 7
                          omega
                        simp [CompCert4Lean.Prototype.dec_Ctypes_member, CodecReference.dec_Ctypes_member, fields, Json.getArr?, previous_dec_Ctypes_signedness, previous_dec_Ctypes_intsize, previous_dec_Ctypes_attr, previous_dec_Ctypes_coq_type, previous_dec_Ctypes_member, wrong3, wrong7]
      | _ => rfl
    · funext value
      cases value with
      | arr values =>
        rcases values with ⟨values⟩
        cases values with
        | nil =>
          simp [CompCert4Lean.Prototype.dec_Ctypes_composite_definition, CodecReference.dec_Ctypes_composite_definition, fields, Json.getArr?, previous_dec_Ctypes_attr, previous_dec_Ctypes_struct_or_union, previous_dec_Ctypes_member, previous_dec_Ctypes_composite_definition]
        | cons head0 tail1 =>
          cases tail1 with
          | nil =>
            cases head0 <;> simp [CompCert4Lean.Prototype.dec_Ctypes_composite_definition, CodecReference.dec_Ctypes_composite_definition, fields, Json.getArr?, previous_dec_Ctypes_attr, previous_dec_Ctypes_struct_or_union, previous_dec_Ctypes_member, previous_dec_Ctypes_composite_definition]
            all_goals split <;> simp_all
          | cons head1 tail2 =>
            cases tail2 with
            | nil =>
              cases head0 <;> simp [CompCert4Lean.Prototype.dec_Ctypes_composite_definition, CodecReference.dec_Ctypes_composite_definition, fields, Json.getArr?, previous_dec_Ctypes_attr, previous_dec_Ctypes_struct_or_union, previous_dec_Ctypes_member, previous_dec_Ctypes_composite_definition]
              all_goals split <;> simp_all
            | cons head2 tail3 =>
              cases tail3 with
              | nil =>
                cases head0 <;> simp [CompCert4Lean.Prototype.dec_Ctypes_composite_definition, CodecReference.dec_Ctypes_composite_definition, fields, Json.getArr?, previous_dec_Ctypes_attr, previous_dec_Ctypes_struct_or_union, previous_dec_Ctypes_member, previous_dec_Ctypes_composite_definition]
                all_goals split <;> simp_all
              | cons head3 tail4 =>
                cases tail4 with
                | nil =>
                  cases head0 <;> simp [CompCert4Lean.Prototype.dec_Ctypes_composite_definition, CodecReference.dec_Ctypes_composite_definition, fields, Json.getArr?, previous_dec_Ctypes_attr, previous_dec_Ctypes_struct_or_union, previous_dec_Ctypes_member, previous_dec_Ctypes_composite_definition]
                  all_goals split <;> simp_all
                | cons head4 tail5 =>
                  cases tail5 with
                  | nil =>
                    cases head0 <;> simp [CompCert4Lean.Prototype.dec_Ctypes_composite_definition, CodecReference.dec_Ctypes_composite_definition, fields, Json.getArr?, previous_dec_Ctypes_attr, previous_dec_Ctypes_struct_or_union, previous_dec_Ctypes_member, previous_dec_Ctypes_composite_definition]
                    all_goals split <;> simp_all
                  | cons head5 tail6 =>
                    have wrong5 : (Array.mk (head0 :: head1 :: head2 :: head3 :: head4 :: head5 :: tail6)).size ≠ 5 := by
                      change tail6.length + 6 ≠ 5
                      omega
                    simp [CompCert4Lean.Prototype.dec_Ctypes_composite_definition, CodecReference.dec_Ctypes_composite_definition, fields, Json.getArr?, previous_dec_Ctypes_attr, previous_dec_Ctypes_struct_or_union, previous_dec_Ctypes_member, previous_dec_Ctypes_composite_definition, wrong5]
      | _ => rfl
    · funext value
      cases value with
      | arr values =>
        rcases values with ⟨values⟩
        cases values with
        | nil =>
          simp [CompCert4Lean.Prototype.dec_Ctypes_bitfield, CodecReference.dec_Ctypes_bitfield, fields, Json.getArr?, previous_dec_Ctypes_signedness, previous_dec_Ctypes_intsize, previous_dec_Ctypes_bitfield]
        | cons head0 tail1 =>
          cases tail1 with
          | nil =>
            cases head0 <;> simp [CompCert4Lean.Prototype.dec_Ctypes_bitfield, CodecReference.dec_Ctypes_bitfield, fields, Json.getArr?, previous_dec_Ctypes_signedness, previous_dec_Ctypes_intsize, previous_dec_Ctypes_bitfield]
            all_goals split <;> simp_all
          | cons head1 tail2 =>
            cases tail2 with
            | nil =>
              cases head0 <;> simp [CompCert4Lean.Prototype.dec_Ctypes_bitfield, CodecReference.dec_Ctypes_bitfield, fields, Json.getArr?, previous_dec_Ctypes_signedness, previous_dec_Ctypes_intsize, previous_dec_Ctypes_bitfield]
              all_goals split <;> simp_all
            | cons head2 tail3 =>
              cases tail3 with
              | nil =>
                cases head0 <;> simp [CompCert4Lean.Prototype.dec_Ctypes_bitfield, CodecReference.dec_Ctypes_bitfield, fields, Json.getArr?, previous_dec_Ctypes_signedness, previous_dec_Ctypes_intsize, previous_dec_Ctypes_bitfield]
                all_goals split <;> simp_all
              | cons head3 tail4 =>
                cases tail4 with
                | nil =>
                  cases head0 <;> simp [CompCert4Lean.Prototype.dec_Ctypes_bitfield, CodecReference.dec_Ctypes_bitfield, fields, Json.getArr?, previous_dec_Ctypes_signedness, previous_dec_Ctypes_intsize, previous_dec_Ctypes_bitfield]
                  all_goals split <;> simp_all
                | cons head4 tail5 =>
                  cases tail5 with
                  | nil =>
                    cases head0 <;> simp [CompCert4Lean.Prototype.dec_Ctypes_bitfield, CodecReference.dec_Ctypes_bitfield, fields, Json.getArr?, previous_dec_Ctypes_signedness, previous_dec_Ctypes_intsize, previous_dec_Ctypes_bitfield]
                    all_goals split <;> simp_all
                  | cons head5 tail6 =>
                    have wrong1 : (Array.mk (head0 :: head1 :: head2 :: head3 :: head4 :: head5 :: tail6)).size ≠ 1 := by
                      change tail6.length + 6 ≠ 1
                      omega
                    have wrong5 : (Array.mk (head0 :: head1 :: head2 :: head3 :: head4 :: head5 :: tail6)).size ≠ 5 := by
                      change tail6.length + 6 ≠ 5
                      omega
                    simp [CompCert4Lean.Prototype.dec_Ctypes_bitfield, CodecReference.dec_Ctypes_bitfield, fields, Json.getArr?, previous_dec_Ctypes_signedness, previous_dec_Ctypes_intsize, previous_dec_Ctypes_bitfield, wrong1, wrong5]
      | _ => rfl
    · funext value
      cases value with
      | arr values =>
        rcases values with ⟨values⟩
        cases values with
        | nil =>
          simp [CompCert4Lean.Prototype.dec_Cop_unary_operation, CodecReference.dec_Cop_unary_operation, fields, Json.getArr?, previous_dec_Cop_unary_operation]
        | cons head0 tail1 =>
          cases tail1 with
          | nil =>
            cases head0 <;> simp [CompCert4Lean.Prototype.dec_Cop_unary_operation, CodecReference.dec_Cop_unary_operation, fields, Json.getArr?, previous_dec_Cop_unary_operation]
            all_goals split <;> simp_all
          | cons head1 tail2 =>
            have wrong1 : (Array.mk (head0 :: head1 :: tail2)).size ≠ 1 := by
              change tail2.length + 2 ≠ 1
              omega
            simp [CompCert4Lean.Prototype.dec_Cop_unary_operation, CodecReference.dec_Cop_unary_operation, fields, Json.getArr?, previous_dec_Cop_unary_operation, wrong1]
      | _ => rfl
    · funext value
      cases value with
      | arr values =>
        rcases values with ⟨values⟩
        cases values with
        | nil =>
          simp [CompCert4Lean.Prototype.dec_Cop_binary_operation, CodecReference.dec_Cop_binary_operation, fields, Json.getArr?, previous_dec_Cop_binary_operation]
        | cons head0 tail1 =>
          cases tail1 with
          | nil =>
            cases head0 <;> simp [CompCert4Lean.Prototype.dec_Cop_binary_operation, CodecReference.dec_Cop_binary_operation, fields, Json.getArr?, previous_dec_Cop_binary_operation]
            all_goals split <;> simp_all
          | cons head1 tail2 =>
            have wrong1 : (Array.mk (head0 :: head1 :: tail2)).size ≠ 1 := by
              change tail2.length + 2 ≠ 1
              omega
            simp [CompCert4Lean.Prototype.dec_Cop_binary_operation, CodecReference.dec_Cop_binary_operation, fields, Json.getArr?, previous_dec_Cop_binary_operation, wrong1]
      | _ => rfl
    · funext value
      cases value with
      | arr values =>
        rcases values with ⟨values⟩
        cases values with
        | nil =>
          simp [CompCert4Lean.Prototype.dec_Cop_incr_or_decr, CodecReference.dec_Cop_incr_or_decr, fields, Json.getArr?, previous_dec_Cop_incr_or_decr]
        | cons head0 tail1 =>
          cases tail1 with
          | nil =>
            cases head0 <;> simp [CompCert4Lean.Prototype.dec_Cop_incr_or_decr, CodecReference.dec_Cop_incr_or_decr, fields, Json.getArr?, previous_dec_Cop_incr_or_decr]
            all_goals split <;> simp_all
          | cons head1 tail2 =>
            have wrong1 : (Array.mk (head0 :: head1 :: tail2)).size ≠ 1 := by
              change tail2.length + 2 ≠ 1
              omega
            simp [CompCert4Lean.Prototype.dec_Cop_incr_or_decr, CodecReference.dec_Cop_incr_or_decr, fields, Json.getArr?, previous_dec_Cop_incr_or_decr, wrong1]
      | _ => rfl
    · funext value
      cases value with
      | arr values =>
        rcases values with ⟨values⟩
        cases values with
        | nil =>
          simp [CompCert4Lean.Prototype.dec_Values_coq_val, CodecReference.dec_Values_coq_val, fields, Json.getArr?, previous_dec_Values_coq_val]
        | cons head0 tail1 =>
          cases tail1 with
          | nil =>
            cases head0 <;> simp [CompCert4Lean.Prototype.dec_Values_coq_val, CodecReference.dec_Values_coq_val, fields, Json.getArr?, previous_dec_Values_coq_val]
            all_goals split <;> simp_all
          | cons head1 tail2 =>
            cases tail2 with
            | nil =>
              cases head0 <;> simp [CompCert4Lean.Prototype.dec_Values_coq_val, CodecReference.dec_Values_coq_val, fields, Json.getArr?, previous_dec_Values_coq_val]
              all_goals split <;> simp_all
            | cons head2 tail3 =>
              cases tail3 with
              | nil =>
                cases head0 <;> simp [CompCert4Lean.Prototype.dec_Values_coq_val, CodecReference.dec_Values_coq_val, fields, Json.getArr?, previous_dec_Values_coq_val]
                all_goals split <;> simp_all
              | cons head3 tail4 =>
                have wrong1 : (Array.mk (head0 :: head1 :: head2 :: head3 :: tail4)).size ≠ 1 := by
                  change tail4.length + 4 ≠ 1
                  omega
                have wrong2 : (Array.mk (head0 :: head1 :: head2 :: head3 :: tail4)).size ≠ 2 := by
                  change tail4.length + 4 ≠ 2
                  omega
                have wrong3 : (Array.mk (head0 :: head1 :: head2 :: head3 :: tail4)).size ≠ 3 := by
                  change tail4.length + 4 ≠ 3
                  omega
                simp [CompCert4Lean.Prototype.dec_Values_coq_val, CodecReference.dec_Values_coq_val, fields, Json.getArr?, previous_dec_Values_coq_val, wrong1, wrong2, wrong3]
      | _ => rfl
    · funext value
      cases value with
      | arr values =>
        rcases values with ⟨values⟩
        cases values with
        | nil =>
          simp [CompCert4Lean.Prototype.dec_Csyntax_expr, CodecReference.dec_Csyntax_expr, fields, Json.getArr?, previous_dec_AST_external_function, previous_dec_Ctypes_coq_type, previous_dec_Ctypes_bitfield, previous_dec_Cop_unary_operation, previous_dec_Cop_binary_operation, previous_dec_Cop_incr_or_decr, previous_dec_Values_coq_val, previous_dec_Csyntax_expr, previous_dec_Csyntax_exprlist]
        | cons head0 tail1 =>
          cases tail1 with
          | nil =>
            cases head0 <;> simp [CompCert4Lean.Prototype.dec_Csyntax_expr, CodecReference.dec_Csyntax_expr, fields, Json.getArr?, previous_dec_AST_external_function, previous_dec_Ctypes_coq_type, previous_dec_Ctypes_bitfield, previous_dec_Cop_unary_operation, previous_dec_Cop_binary_operation, previous_dec_Cop_incr_or_decr, previous_dec_Values_coq_val, previous_dec_Csyntax_expr, previous_dec_Csyntax_exprlist]
            all_goals split <;> simp_all
          | cons head1 tail2 =>
            cases tail2 with
            | nil =>
              cases head0 <;> simp [CompCert4Lean.Prototype.dec_Csyntax_expr, CodecReference.dec_Csyntax_expr, fields, Json.getArr?, previous_dec_AST_external_function, previous_dec_Ctypes_coq_type, previous_dec_Ctypes_bitfield, previous_dec_Cop_unary_operation, previous_dec_Cop_binary_operation, previous_dec_Cop_incr_or_decr, previous_dec_Values_coq_val, previous_dec_Csyntax_expr, previous_dec_Csyntax_exprlist]
              all_goals split <;> simp_all
            | cons head2 tail3 =>
              cases tail3 with
              | nil =>
                cases head0 <;> simp [CompCert4Lean.Prototype.dec_Csyntax_expr, CodecReference.dec_Csyntax_expr, fields, Json.getArr?, previous_dec_AST_external_function, previous_dec_Ctypes_coq_type, previous_dec_Ctypes_bitfield, previous_dec_Cop_unary_operation, previous_dec_Cop_binary_operation, previous_dec_Cop_incr_or_decr, previous_dec_Values_coq_val, previous_dec_Csyntax_expr, previous_dec_Csyntax_exprlist]
                all_goals split <;> simp_all
              | cons head3 tail4 =>
                cases tail4 with
                | nil =>
                  cases head0 <;> simp [CompCert4Lean.Prototype.dec_Csyntax_expr, CodecReference.dec_Csyntax_expr, fields, Json.getArr?, previous_dec_AST_external_function, previous_dec_Ctypes_coq_type, previous_dec_Ctypes_bitfield, previous_dec_Cop_unary_operation, previous_dec_Cop_binary_operation, previous_dec_Cop_incr_or_decr, previous_dec_Values_coq_val, previous_dec_Csyntax_expr, previous_dec_Csyntax_exprlist]
                  all_goals split <;> simp_all
                | cons head4 tail5 =>
                  cases tail5 with
                  | nil =>
                    cases head0 <;> simp [CompCert4Lean.Prototype.dec_Csyntax_expr, CodecReference.dec_Csyntax_expr, fields, Json.getArr?, previous_dec_AST_external_function, previous_dec_Ctypes_coq_type, previous_dec_Ctypes_bitfield, previous_dec_Cop_unary_operation, previous_dec_Cop_binary_operation, previous_dec_Cop_incr_or_decr, previous_dec_Values_coq_val, previous_dec_Csyntax_expr, previous_dec_Csyntax_exprlist]
                    all_goals split <;> simp_all
                  | cons head5 tail6 =>
                    cases tail6 with
                    | nil =>
                      cases head0 <;> simp [CompCert4Lean.Prototype.dec_Csyntax_expr, CodecReference.dec_Csyntax_expr, fields, Json.getArr?, previous_dec_AST_external_function, previous_dec_Ctypes_coq_type, previous_dec_Ctypes_bitfield, previous_dec_Cop_unary_operation, previous_dec_Cop_binary_operation, previous_dec_Cop_incr_or_decr, previous_dec_Values_coq_val, previous_dec_Csyntax_expr, previous_dec_Csyntax_exprlist]
                      all_goals split <;> simp_all
                    | cons head6 tail7 =>
                      have wrong3 : (Array.mk (head0 :: head1 :: head2 :: head3 :: head4 :: head5 :: head6 :: tail7)).size ≠ 3 := by
                        change tail7.length + 7 ≠ 3
                        omega
                      have wrong4 : (Array.mk (head0 :: head1 :: head2 :: head3 :: head4 :: head5 :: head6 :: tail7)).size ≠ 4 := by
                        change tail7.length + 7 ≠ 4
                        omega
                      have wrong5 : (Array.mk (head0 :: head1 :: head2 :: head3 :: head4 :: head5 :: head6 :: tail7)).size ≠ 5 := by
                        change tail7.length + 7 ≠ 5
                        omega
                      have wrong6 : (Array.mk (head0 :: head1 :: head2 :: head3 :: head4 :: head5 :: head6 :: tail7)).size ≠ 6 := by
                        change tail7.length + 7 ≠ 6
                        omega
                      simp [CompCert4Lean.Prototype.dec_Csyntax_expr, CodecReference.dec_Csyntax_expr, fields, Json.getArr?, previous_dec_AST_external_function, previous_dec_Ctypes_coq_type, previous_dec_Ctypes_bitfield, previous_dec_Cop_unary_operation, previous_dec_Cop_binary_operation, previous_dec_Cop_incr_or_decr, previous_dec_Values_coq_val, previous_dec_Csyntax_expr, previous_dec_Csyntax_exprlist, wrong3, wrong4, wrong5, wrong6]
      | _ => rfl
    · funext value
      cases value with
      | arr values =>
        rcases values with ⟨values⟩
        cases values with
        | nil =>
          simp [CompCert4Lean.Prototype.dec_Csyntax_exprlist, CodecReference.dec_Csyntax_exprlist, fields, Json.getArr?, previous_dec_Csyntax_expr, previous_dec_Csyntax_exprlist]
        | cons head0 tail1 =>
          cases tail1 with
          | nil =>
            cases head0 <;> simp [CompCert4Lean.Prototype.dec_Csyntax_exprlist, CodecReference.dec_Csyntax_exprlist, fields, Json.getArr?, previous_dec_Csyntax_expr, previous_dec_Csyntax_exprlist]
            all_goals split <;> simp_all
          | cons head1 tail2 =>
            cases tail2 with
            | nil =>
              cases head0 <;> simp [CompCert4Lean.Prototype.dec_Csyntax_exprlist, CodecReference.dec_Csyntax_exprlist, fields, Json.getArr?, previous_dec_Csyntax_expr, previous_dec_Csyntax_exprlist]
              all_goals split <;> simp_all
            | cons head2 tail3 =>
              cases tail3 with
              | nil =>
                cases head0 <;> simp [CompCert4Lean.Prototype.dec_Csyntax_exprlist, CodecReference.dec_Csyntax_exprlist, fields, Json.getArr?, previous_dec_Csyntax_expr, previous_dec_Csyntax_exprlist]
                all_goals split <;> simp_all
              | cons head3 tail4 =>
                have wrong1 : (Array.mk (head0 :: head1 :: head2 :: head3 :: tail4)).size ≠ 1 := by
                  change tail4.length + 4 ≠ 1
                  omega
                have wrong3 : (Array.mk (head0 :: head1 :: head2 :: head3 :: tail4)).size ≠ 3 := by
                  change tail4.length + 4 ≠ 3
                  omega
                simp [CompCert4Lean.Prototype.dec_Csyntax_exprlist, CodecReference.dec_Csyntax_exprlist, fields, Json.getArr?, previous_dec_Csyntax_expr, previous_dec_Csyntax_exprlist, wrong1, wrong3]
      | _ => rfl
    · funext value
      cases value with
      | arr values =>
        rcases values with ⟨values⟩
        cases values with
        | nil =>
          simp [CompCert4Lean.Prototype.dec_Csyntax_statement, CodecReference.dec_Csyntax_statement, fields, Json.getArr?, previous_dec_Csyntax_expr, previous_dec_Csyntax_statement, previous_dec_Csyntax_labeled_statements]
        | cons head0 tail1 =>
          cases tail1 with
          | nil =>
            cases head0 <;> simp [CompCert4Lean.Prototype.dec_Csyntax_statement, CodecReference.dec_Csyntax_statement, fields, Json.getArr?, previous_dec_Csyntax_expr, previous_dec_Csyntax_statement, previous_dec_Csyntax_labeled_statements]
            all_goals split <;> simp_all
          | cons head1 tail2 =>
            cases tail2 with
            | nil =>
              cases head0 <;> simp [CompCert4Lean.Prototype.dec_Csyntax_statement, CodecReference.dec_Csyntax_statement, fields, Json.getArr?, previous_dec_Csyntax_expr, previous_dec_Csyntax_statement, previous_dec_Csyntax_labeled_statements]
              all_goals split <;> simp_all
            | cons head2 tail3 =>
              cases tail3 with
              | nil =>
                cases head0 <;> simp [CompCert4Lean.Prototype.dec_Csyntax_statement, CodecReference.dec_Csyntax_statement, fields, Json.getArr?, previous_dec_Csyntax_expr, previous_dec_Csyntax_statement, previous_dec_Csyntax_labeled_statements]
                all_goals split <;> simp_all
              | cons head3 tail4 =>
                cases tail4 with
                | nil =>
                  cases head0 <;> simp [CompCert4Lean.Prototype.dec_Csyntax_statement, CodecReference.dec_Csyntax_statement, fields, Json.getArr?, previous_dec_Csyntax_expr, previous_dec_Csyntax_statement, previous_dec_Csyntax_labeled_statements]
                  all_goals split <;> simp_all
                | cons head4 tail5 =>
                  cases tail5 with
                  | nil =>
                    cases head0 <;> simp [CompCert4Lean.Prototype.dec_Csyntax_statement, CodecReference.dec_Csyntax_statement, fields, Json.getArr?, previous_dec_Csyntax_expr, previous_dec_Csyntax_statement, previous_dec_Csyntax_labeled_statements]
                    all_goals split <;> simp_all
                  | cons head5 tail6 =>
                    have wrong1 : (Array.mk (head0 :: head1 :: head2 :: head3 :: head4 :: head5 :: tail6)).size ≠ 1 := by
                      change tail6.length + 6 ≠ 1
                      omega
                    have wrong2 : (Array.mk (head0 :: head1 :: head2 :: head3 :: head4 :: head5 :: tail6)).size ≠ 2 := by
                      change tail6.length + 6 ≠ 2
                      omega
                    have wrong3 : (Array.mk (head0 :: head1 :: head2 :: head3 :: head4 :: head5 :: tail6)).size ≠ 3 := by
                      change tail6.length + 6 ≠ 3
                      omega
                    have wrong4 : (Array.mk (head0 :: head1 :: head2 :: head3 :: head4 :: head5 :: tail6)).size ≠ 4 := by
                      change tail6.length + 6 ≠ 4
                      omega
                    have wrong5 : (Array.mk (head0 :: head1 :: head2 :: head3 :: head4 :: head5 :: tail6)).size ≠ 5 := by
                      change tail6.length + 6 ≠ 5
                      omega
                    simp [CompCert4Lean.Prototype.dec_Csyntax_statement, CodecReference.dec_Csyntax_statement, fields, Json.getArr?, previous_dec_Csyntax_expr, previous_dec_Csyntax_statement, previous_dec_Csyntax_labeled_statements, wrong1, wrong2, wrong3, wrong4, wrong5]
      | _ => rfl
    · funext value
      cases value with
      | arr values =>
        rcases values with ⟨values⟩
        cases values with
        | nil =>
          simp [CompCert4Lean.Prototype.dec_Csyntax_labeled_statements, CodecReference.dec_Csyntax_labeled_statements, fields, Json.getArr?, previous_dec_Csyntax_statement, previous_dec_Csyntax_labeled_statements]
        | cons head0 tail1 =>
          cases tail1 with
          | nil =>
            cases head0 <;> simp [CompCert4Lean.Prototype.dec_Csyntax_labeled_statements, CodecReference.dec_Csyntax_labeled_statements, fields, Json.getArr?, previous_dec_Csyntax_statement, previous_dec_Csyntax_labeled_statements]
            all_goals split <;> simp_all
          | cons head1 tail2 =>
            cases tail2 with
            | nil =>
              cases head0 <;> simp [CompCert4Lean.Prototype.dec_Csyntax_labeled_statements, CodecReference.dec_Csyntax_labeled_statements, fields, Json.getArr?, previous_dec_Csyntax_statement, previous_dec_Csyntax_labeled_statements]
              all_goals split <;> simp_all
            | cons head2 tail3 =>
              cases tail3 with
              | nil =>
                cases head0 <;> simp [CompCert4Lean.Prototype.dec_Csyntax_labeled_statements, CodecReference.dec_Csyntax_labeled_statements, fields, Json.getArr?, previous_dec_Csyntax_statement, previous_dec_Csyntax_labeled_statements]
                all_goals split <;> simp_all
              | cons head3 tail4 =>
                cases tail4 with
                | nil =>
                  cases head0 <;> simp [CompCert4Lean.Prototype.dec_Csyntax_labeled_statements, CodecReference.dec_Csyntax_labeled_statements, fields, Json.getArr?, previous_dec_Csyntax_statement, previous_dec_Csyntax_labeled_statements]
                  all_goals split <;> simp_all
                | cons head4 tail5 =>
                  have wrong1 : (Array.mk (head0 :: head1 :: head2 :: head3 :: head4 :: tail5)).size ≠ 1 := by
                    change tail5.length + 5 ≠ 1
                    omega
                  have wrong4 : (Array.mk (head0 :: head1 :: head2 :: head3 :: head4 :: tail5)).size ≠ 4 := by
                    change tail5.length + 5 ≠ 4
                    omega
                  simp [CompCert4Lean.Prototype.dec_Csyntax_labeled_statements, CodecReference.dec_Csyntax_labeled_statements, fields, Json.getArr?, previous_dec_Csyntax_statement, previous_dec_Csyntax_labeled_statements, wrong1, wrong4]
      | _ => rfl
    · funext value
      cases value with
      | arr values =>
        rcases values with ⟨values⟩
        cases values with
        | nil =>
          simp [CompCert4Lean.Prototype.dec_Csyntax_coq_function, CodecReference.dec_Csyntax_coq_function, fields, Json.getArr?, previous_dec_AST_calling_convention, previous_dec_Ctypes_coq_type, previous_dec_Csyntax_statement, previous_dec_Csyntax_coq_function]
        | cons head0 tail1 =>
          cases tail1 with
          | nil =>
            cases head0 <;> simp [CompCert4Lean.Prototype.dec_Csyntax_coq_function, CodecReference.dec_Csyntax_coq_function, fields, Json.getArr?, previous_dec_AST_calling_convention, previous_dec_Ctypes_coq_type, previous_dec_Csyntax_statement, previous_dec_Csyntax_coq_function]
            all_goals split <;> simp_all
          | cons head1 tail2 =>
            cases tail2 with
            | nil =>
              cases head0 <;> simp [CompCert4Lean.Prototype.dec_Csyntax_coq_function, CodecReference.dec_Csyntax_coq_function, fields, Json.getArr?, previous_dec_AST_calling_convention, previous_dec_Ctypes_coq_type, previous_dec_Csyntax_statement, previous_dec_Csyntax_coq_function]
              all_goals split <;> simp_all
            | cons head2 tail3 =>
              cases tail3 with
              | nil =>
                cases head0 <;> simp [CompCert4Lean.Prototype.dec_Csyntax_coq_function, CodecReference.dec_Csyntax_coq_function, fields, Json.getArr?, previous_dec_AST_calling_convention, previous_dec_Ctypes_coq_type, previous_dec_Csyntax_statement, previous_dec_Csyntax_coq_function]
                all_goals split <;> simp_all
              | cons head3 tail4 =>
                cases tail4 with
                | nil =>
                  cases head0 <;> simp [CompCert4Lean.Prototype.dec_Csyntax_coq_function, CodecReference.dec_Csyntax_coq_function, fields, Json.getArr?, previous_dec_AST_calling_convention, previous_dec_Ctypes_coq_type, previous_dec_Csyntax_statement, previous_dec_Csyntax_coq_function]
                  all_goals split <;> simp_all
                | cons head4 tail5 =>
                  cases tail5 with
                  | nil =>
                    cases head0 <;> simp [CompCert4Lean.Prototype.dec_Csyntax_coq_function, CodecReference.dec_Csyntax_coq_function, fields, Json.getArr?, previous_dec_AST_calling_convention, previous_dec_Ctypes_coq_type, previous_dec_Csyntax_statement, previous_dec_Csyntax_coq_function]
                    all_goals split <;> simp_all
                  | cons head5 tail6 =>
                    cases tail6 with
                    | nil =>
                      cases head0 <;> simp [CompCert4Lean.Prototype.dec_Csyntax_coq_function, CodecReference.dec_Csyntax_coq_function, fields, Json.getArr?, previous_dec_AST_calling_convention, previous_dec_Ctypes_coq_type, previous_dec_Csyntax_statement, previous_dec_Csyntax_coq_function]
                      all_goals split <;> simp_all
                    | cons head6 tail7 =>
                      have wrong6 : (Array.mk (head0 :: head1 :: head2 :: head3 :: head4 :: head5 :: head6 :: tail7)).size ≠ 6 := by
                        change tail7.length + 7 ≠ 6
                        omega
                      simp [CompCert4Lean.Prototype.dec_Csyntax_coq_function, CodecReference.dec_Csyntax_coq_function, fields, Json.getArr?, previous_dec_AST_calling_convention, previous_dec_Ctypes_coq_type, previous_dec_Csyntax_statement, previous_dec_Csyntax_coq_function, wrong6]
      | _ => rfl
    · funext value
      cases value with
      | arr values =>
        rcases values with ⟨values⟩
        cases values with
        | nil =>
          simp [CompCert4Lean.Prototype.dec_CFundef, CodecReference.dec_CFundef, fields, Json.getArr?, previous_dec_AST_calling_convention, previous_dec_AST_external_function, previous_dec_Ctypes_coq_type, previous_dec_Csyntax_coq_function, previous_dec_CFundef]
        | cons head0 tail1 =>
          cases tail1 with
          | nil =>
            cases head0 <;> simp [CompCert4Lean.Prototype.dec_CFundef, CodecReference.dec_CFundef, fields, Json.getArr?, previous_dec_AST_calling_convention, previous_dec_AST_external_function, previous_dec_Ctypes_coq_type, previous_dec_Csyntax_coq_function, previous_dec_CFundef]
            all_goals split <;> simp_all
          | cons head1 tail2 =>
            cases tail2 with
            | nil =>
              cases head0 <;> simp [CompCert4Lean.Prototype.dec_CFundef, CodecReference.dec_CFundef, fields, Json.getArr?, previous_dec_AST_calling_convention, previous_dec_AST_external_function, previous_dec_Ctypes_coq_type, previous_dec_Csyntax_coq_function, previous_dec_CFundef]
              all_goals split <;> simp_all
            | cons head2 tail3 =>
              cases tail3 with
              | nil =>
                cases head0 <;> simp [CompCert4Lean.Prototype.dec_CFundef, CodecReference.dec_CFundef, fields, Json.getArr?, previous_dec_AST_calling_convention, previous_dec_AST_external_function, previous_dec_Ctypes_coq_type, previous_dec_Csyntax_coq_function, previous_dec_CFundef]
                all_goals split <;> simp_all
              | cons head3 tail4 =>
                cases tail4 with
                | nil =>
                  cases head0 <;> simp [CompCert4Lean.Prototype.dec_CFundef, CodecReference.dec_CFundef, fields, Json.getArr?, previous_dec_AST_calling_convention, previous_dec_AST_external_function, previous_dec_Ctypes_coq_type, previous_dec_Csyntax_coq_function, previous_dec_CFundef]
                  all_goals split <;> simp_all
                | cons head4 tail5 =>
                  cases tail5 with
                  | nil =>
                    cases head0 <;> simp [CompCert4Lean.Prototype.dec_CFundef, CodecReference.dec_CFundef, fields, Json.getArr?, previous_dec_AST_calling_convention, previous_dec_AST_external_function, previous_dec_Ctypes_coq_type, previous_dec_Csyntax_coq_function, previous_dec_CFundef]
                    all_goals split <;> simp_all
                  | cons head5 tail6 =>
                    have wrong2 : (Array.mk (head0 :: head1 :: head2 :: head3 :: head4 :: head5 :: tail6)).size ≠ 2 := by
                      change tail6.length + 6 ≠ 2
                      omega
                    have wrong5 : (Array.mk (head0 :: head1 :: head2 :: head3 :: head4 :: head5 :: tail6)).size ≠ 5 := by
                      change tail6.length + 6 ≠ 5
                      omega
                    simp [CompCert4Lean.Prototype.dec_CFundef, CodecReference.dec_CFundef, fields, Json.getArr?, previous_dec_AST_calling_convention, previous_dec_AST_external_function, previous_dec_Ctypes_coq_type, previous_dec_Csyntax_coq_function, previous_dec_CFundef, wrong2, wrong5]
      | _ => rfl
    · funext value
      cases value with
      | arr values =>
        rcases values with ⟨values⟩
        cases values with
        | nil =>
          simp [CompCert4Lean.Prototype.dec_CGlobvar, CodecReference.dec_CGlobvar, fields, Json.getArr?, previous_dec_AST_init_data, previous_dec_Ctypes_coq_type, previous_dec_CGlobvar]
        | cons head0 tail1 =>
          cases tail1 with
          | nil =>
            cases head0 <;> simp [CompCert4Lean.Prototype.dec_CGlobvar, CodecReference.dec_CGlobvar, fields, Json.getArr?, previous_dec_AST_init_data, previous_dec_Ctypes_coq_type, previous_dec_CGlobvar]
            all_goals split <;> simp_all
          | cons head1 tail2 =>
            cases tail2 with
            | nil =>
              cases head0 <;> simp [CompCert4Lean.Prototype.dec_CGlobvar, CodecReference.dec_CGlobvar, fields, Json.getArr?, previous_dec_AST_init_data, previous_dec_Ctypes_coq_type, previous_dec_CGlobvar]
              all_goals split <;> simp_all
            | cons head2 tail3 =>
              cases tail3 with
              | nil =>
                cases head0 <;> simp [CompCert4Lean.Prototype.dec_CGlobvar, CodecReference.dec_CGlobvar, fields, Json.getArr?, previous_dec_AST_init_data, previous_dec_Ctypes_coq_type, previous_dec_CGlobvar]
                all_goals split <;> simp_all
              | cons head3 tail4 =>
                cases tail4 with
                | nil =>
                  cases head0 <;> simp [CompCert4Lean.Prototype.dec_CGlobvar, CodecReference.dec_CGlobvar, fields, Json.getArr?, previous_dec_AST_init_data, previous_dec_Ctypes_coq_type, previous_dec_CGlobvar]
                  all_goals split <;> simp_all
                | cons head4 tail5 =>
                  cases tail5 with
                  | nil =>
                    cases head0 <;> simp [CompCert4Lean.Prototype.dec_CGlobvar, CodecReference.dec_CGlobvar, fields, Json.getArr?, previous_dec_AST_init_data, previous_dec_Ctypes_coq_type, previous_dec_CGlobvar]
                    all_goals split <;> simp_all
                  | cons head5 tail6 =>
                    have wrong5 : (Array.mk (head0 :: head1 :: head2 :: head3 :: head4 :: head5 :: tail6)).size ≠ 5 := by
                      change tail6.length + 6 ≠ 5
                      omega
                    simp [CompCert4Lean.Prototype.dec_CGlobvar, CodecReference.dec_CGlobvar, fields, Json.getArr?, previous_dec_AST_init_data, previous_dec_Ctypes_coq_type, previous_dec_CGlobvar, wrong5]
      | _ => rfl
    · funext value
      cases value with
      | arr values =>
        rcases values with ⟨values⟩
        cases values with
        | nil =>
          simp [CompCert4Lean.Prototype.dec_CGlobdef, CodecReference.dec_CGlobdef, fields, Json.getArr?, previous_dec_CFundef, previous_dec_CGlobvar, previous_dec_CGlobdef]
        | cons head0 tail1 =>
          cases tail1 with
          | nil =>
            cases head0 <;> simp [CompCert4Lean.Prototype.dec_CGlobdef, CodecReference.dec_CGlobdef, fields, Json.getArr?, previous_dec_CFundef, previous_dec_CGlobvar, previous_dec_CGlobdef]
            all_goals split <;> simp_all
          | cons head1 tail2 =>
            cases tail2 with
            | nil =>
              cases head0 <;> simp [CompCert4Lean.Prototype.dec_CGlobdef, CodecReference.dec_CGlobdef, fields, Json.getArr?, previous_dec_CFundef, previous_dec_CGlobvar, previous_dec_CGlobdef]
              all_goals split <;> simp_all
            | cons head2 tail3 =>
              have wrong2 : (Array.mk (head0 :: head1 :: head2 :: tail3)).size ≠ 2 := by
                change tail3.length + 3 ≠ 2
                omega
              simp [CompCert4Lean.Prototype.dec_CGlobdef, CodecReference.dec_CGlobdef, fields, Json.getArr?, previous_dec_CFundef, previous_dec_CGlobvar, previous_dec_CGlobdef, wrong2]
      | _ => rfl

#print axioms indexed_decoders_eq
