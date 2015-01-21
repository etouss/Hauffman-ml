(* This code was written by Juliusz Chroboczek.  MIT license. modified by Adequin Toussaint*)

type 'a bit_channel = {chan : 'a;
                       mutable byte : int;
                       mutable len: int}

type bit_in_channel = in_channel bit_channel
type bit_out_channel = out_channel bit_channel

let open_in_bit filename =
  { chan = open_in_bin filename; byte = 0; len = 0 }

let open_out_bit filename =
  { chan = open_out_bin filename; byte = 0; len = 0 }

let input_bit chan = try begin
  let input_bit2 chan2 =
    (if chan.len = 0
     then let byte = input_byte chan.chan in
          (chan.byte <- byte; chan.len <- 8));
    let bit = (chan.byte lsr (chan.len - 1)) land 1 in
    (chan.len <- chan.len - 1;
     bit) in input_bit2 chan
  end
with
|End_of_file -> 256


let input_bit_byte chan = try begin
  let input_bit_byte2 chan2 =
    if chan.len = 0 then
      input_byte chan.chan
    else
      let rec ibb i b =
        if i < 8
        then ibb (i + 1) (b lor ((input_bit chan) lsl (7 - i)))
        else b
      in ibb 0 0 in input_bit_byte2 chan
  end
with
|End_of_file -> 256


let input_align_bit chan =
  while chan.len <> 0 do
    ignore (input_bit chan)
  done

let output_bit chan bit =
  assert (bit = 0 || bit = 1);
  chan.byte <- (chan.byte lsl 1) lor bit;
  chan.len <- chan.len + 1;
  if chan.len = 8
  then (output_byte chan.chan chan.byte;
        chan.byte <- 0;
        chan.len <- 0)


let output_bit_byte chan byte =
  assert (byte >= 0 && byte < 256);
  if chan.len = 0 then
    output_byte chan.chan byte
  else
    for i = 0 to 7 do
      output_bit chan ((byte lsr (7 - i)) land 1)
    done


let output_align_bit chan =
  while chan.len <> 0 do
    output_bit chan 0
  done

let close_in_bit chan =
  close_in chan.chan

let close_out_bit chan =
  output_align_bit chan;
  close_out chan.chan
