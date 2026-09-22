let node tag fields = `List (`String tag :: fields)
let enc_list encode values = `List (List.map encode values)
let dec_list decode = function `List values -> List.map decode values | _ -> failwith "expected list"
let enc_option encode = function None -> `Null | Some value -> encode value
let dec_option decode = function `Null -> None | value -> Some (decode value)
let enc_pair first second (left, right) = `List [first left; second right]
let dec_pair first second = function
  | `List [left; right] -> (first left, second right)
  | _ -> failwith "expected pair"
let enc_sum left right = function
  | Datatypes.Coq_inl value -> node "inl" [left value]
  | Datatypes.Coq_inr value -> node "inr" [right value]
let dec_sum left right = function
  | `List [`String "inl"; value] -> Datatypes.Coq_inl (left value)
  | `List [`String "inr"; value] -> Datatypes.Coq_inr (right value)
  | _ -> failwith "expected sum"
let enc_bool value = `Bool value
let dec_bool = function `Bool value -> value | _ -> failwith "expected boolean"
let enc_unit () = `Null
let dec_unit = function `Null -> () | _ -> failwith "expected unit"
let rec positive_to_z = function
  | BinNums.Coq_xH -> Z.one
  | BinNums.Coq_xO rest -> Z.shift_left (positive_to_z rest) 1
  | BinNums.Coq_xI rest -> Z.succ (Z.shift_left (positive_to_z rest) 1)
let rec positive_of_z number =
  if Z.equal number Z.one then BinNums.Coq_xH
  else if Z.testbit number 0 then BinNums.Coq_xI (positive_of_z (Z.shift_right number 1))
  else BinNums.Coq_xO (positive_of_z (Z.shift_right number 1))
let decimal = function
  | `String text ->
      let number = Z.of_string text in
      if Z.to_string number <> text then failwith "noncanonical integer";
      number
  | _ -> failwith "expected decimal string"
let enc_pos value = `String (Z.to_string (positive_to_z value))
let dec_pos value =
  let number = decimal value in
  if Z.sign number <= 0 then failwith "identifier must be positive";
  positive_of_z number
let z_to_z = function
  | BinNums.Z0 -> Z.zero
  | BinNums.Zpos value -> positive_to_z value
  | BinNums.Zneg value -> Z.neg (positive_to_z value)
let z_of_z number =
  match Z.sign number with
  | 0 -> BinNums.Z0
  | 1 -> BinNums.Zpos (positive_of_z number)
  | _ -> BinNums.Zneg (positive_of_z (Z.neg number))
let enc_z value = `String (Z.to_string (z_to_z value))
let dec_z value = z_of_z (decimal value)
let enc_n = function BinNums.N0 -> `String "0" | BinNums.Npos value -> enc_pos value
let dec_n value =
  let number = decimal value in
  if Z.sign number < 0 then failwith "expected nonnegative integer";
  if Z.equal number Z.zero then BinNums.N0 else BinNums.Npos (positive_of_z number)
let bounded bits value =
  let number = decimal value in
  if Z.sign number < 0 || Z.compare number (Z.shift_left Z.one bits) >= 0
  then failwith "integer bit width exceeded";
  z_of_z number
let enc_int value = enc_z (Integers.Int.unsigned value)
let dec_int value = Integers.Int.repr (bounded 32 value)
let enc_long value = enc_z (Integers.Int64.unsigned value)
let dec_long value = Integers.Int64.repr (bounded 64 value)
let enc_ptr value = enc_z (Integers.Ptrofs.unsigned value)
let dec_ptr value = Integers.Ptrofs.repr (bounded 64 value)
let enc_float value = enc_long (Floats.Float.to_bits value)
let dec_float value = Floats.Float.of_bits (dec_long value)
let enc_single value = enc_int (Floats.Float32.to_bits value)
let dec_single value = Floats.Float32.of_bits (dec_int value)
let enc_string value = `List (List.init (String.length value) (fun index -> `Int (Char.code value.[index])))
let dec_string = function
  | `List bytes -> String.of_seq (List.to_seq (List.map (function
      | `Int number when number >= 0 && number < 256 -> Char.chr number
      | _ -> failwith "invalid byte") bytes))
  | _ -> failwith "expected byte string"
