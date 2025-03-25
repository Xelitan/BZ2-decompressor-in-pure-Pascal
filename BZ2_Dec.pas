unit BZ2_Dec;

////////////////////////////////////////////////////////////////////////////////
//                                                                            //
// Description:	BZip2 decompressor in pure Pascal                             //
// Version:	0.1                                                           //
// Date:	25-MAR-2025                                                   //
// License:     LGPLv2                                                        //
// Target:	Win64, Free Pascal, Delphi                                    //
// Based on:    micro bunzip by Rob Landley (LGPLv2)                          //
// Copyright:	(c) 2025 Xelitan.com.                                         //
//		All rights reserved.                                          //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////


{$mode objfpc}{$H+}

interface

uses
  SysUtils, Classes;

const
  // Constants for huffman coding
  MAX_GROUPS = 6;
  GROUP_SIZE = 50;
  MAX_HUFCODE_BITS = 20;  // Longest huffman code allowed
  MAX_SYMBOLS = 258;  // 256 literals + RUNA + RUNB
  SYMBOL_RUNA = 0;
  SYMBOL_RUNB = 1;

  // Status return values
  RETVAL_OK = 0;
  RETVAL_LAST_BLOCK = -1;
  RETVAL_NOT_BZIP_DATA = -2;
  RETVAL_UNEXPECTED_INPUT_EOF = -3;
  RETVAL_UNEXPECTED_OUTPUT_EOF = -4;
  RETVAL_DATA_ERROR = -5;
  RETVAL_OUT_OF_MEMORY = -6;
  RETVAL_OBSOLETE_INPUT = -7;

  // Other housekeeping constants
  IOBUFF_SIZE = 4096;

type
  PGroupData = ^TGroupData;
  TGroupData = record
    // We have an extra slot at the end of limit[] for a sentinal value.
    limit: array[0..MAX_HUFCODE_BITS] of Integer;
    base: array[0..MAX_HUFCODE_BITS-1] of Integer;
    permute: array[0..MAX_SYMBOLS-1] of Integer;
    minLen, maxLen: Integer;
  end;

  Pbunzip_data = ^Tbunzip_data;
  Tbunzip_data = record
    // State for interrupting output loop
    writeCopies, writePos, writeRunCountdown, writeCount, writeCurrent: Integer;
    // I/O tracking data (file handles, buffers, positions, etc.)
    in_fd, out_fd: TFileStream;
    inbufCount, inbufPos: Integer;
    inbuf: PByte;
    inbufBitCount, inbufBits: Cardinal;
    // The CRC values stored in the block header and calculated from the data
    crc32Table: array[0..255] of Cardinal;
    headerCRC, totalCRC, writeCRC: Cardinal;
    // Intermediate buffer and its size (in bytes)
    dbuf: PCardinal;
    dbufSize: Cardinal;
    // These things are a bit too big to go on the stack
    selectors: array[0..32767] of Byte;   // nSelectors=15 bits
    groups: array[0..MAX_GROUPS-1] of TGroupData; // huffman coding tables
    // For I/O error handling
    jmpbuf: jmp_buf;
  end;

function BZ2DecompressStream(InStream, OutStream: TFileStream): Integer;

implementation

function get_bits(bd: Pbunzip_data; bits_wanted: Integer): Cardinal; forward;
function get_next_block(bd: Pbunzip_data): Integer; forward;

function get_bits(bd: Pbunzip_data; bits_wanted: Integer): Cardinal;
var
  bits: Cardinal;
  k: Integer;
begin
  bits := 0;

  while bd^.inbufBitCount < bits_wanted do
  begin
    if bd^.inbufPos = bd^.inbufCount then
    begin
      bd^.inbufCount := bd^.in_fd.Read(bd^.inbuf^, IOBUFF_SIZE);
      if bd^.inbufCount <= 0 then
        longjmp(bd^.jmpbuf, RETVAL_UNEXPECTED_INPUT_EOF);
      bd^.inbufPos := 0;
    end;

    if bd^.inbufBitCount >= 24 then
    begin
      bits := bd^.inbufBits and ((1 shl bd^.inbufBitCount) - 1);
      Dec(bits_wanted, bd^.inbufBitCount);
      bits := bits shl bits_wanted;
      bd^.inbufBitCount := 0;
    end;

    bd^.inbufBits := (bd^.inbufBits shl 8) or bd^.inbuf[bd^.inbufPos];
    Inc(bd^.inbufPos);
    Inc(bd^.inbufBitCount, 8);
  end;

  Dec(bd^.inbufBitCount, bits_wanted);
  bits := bits or ((bd^.inbufBits shr bd^.inbufBitCount) and ((1 shl bits_wanted) - 1));

  Result := bits;
end;

function get_next_block(bd: Pbunzip_data): Integer;
var
  hufGroup: PGroupData;
  dbufCount, nextSym, dbufSize, groupCount, selector: Integer;
  i, j, k, t, runPos, symCount, symTotal, nSelectors: Integer;
  origPtr: Cardinal;
  uc: Byte;
  symToByte, mtfSymbol: array[0..255] of Byte;
  selectors: PByte;
  dbuf: PCardinal;
  byteCount: array[0..255] of Integer;
  base, limit: PInteger;
  length: array[0..MAX_SYMBOLS-1] of Byte;
  temp: array[0..MAX_HUFCODE_BITS] of Integer;
  minLen, maxLen, pp: Integer;
  huffBitsReceived: Boolean;
begin
  dbuf := bd^.dbuf;
  dbufSize := bd^.dbufSize;
  selectors := @bd^.selectors[0];

  i := setjmp(bd^.jmpbuf);
  if i <> 0 then
  begin
    Result := i;
    Exit;
  end;

  i := get_bits(bd, 24);
  j := get_bits(bd, 24);
  bd^.headerCRC := get_bits(bd, 32);
  if (i = $177245) and (j = $385090) then
  begin
    Result := RETVAL_LAST_BLOCK;
    Exit;
  end;
  if (i <> $314159) or (j <> $265359) then
  begin
    Result := RETVAL_NOT_BZIP_DATA;
    Exit;
  end;

  if get_bits(bd, 1) <> 0 then
  begin
    Result := RETVAL_OBSOLETE_INPUT;
    Exit;
  end;

  origPtr := get_bits(bd, 24);
  if origPtr > dbufSize then
  begin
    Result := RETVAL_DATA_ERROR;
    Exit;
  end;

  t := get_bits(bd, 16);
  symTotal := 0;
  for i := 0 to 15 do
  begin
    if (t and (1 shl (15 - i))) <> 0 then
    begin
      k := get_bits(bd, 16);
      for j := 0 to 15 do
        if (k and (1 shl (15 - j))) <> 0 then
        begin
          symToByte[symTotal] := (16 * i) + j;
          Inc(symTotal);
        end;
    end;
  end;

  groupCount := get_bits(bd, 3);
  if (groupCount < 2) or (groupCount > MAX_GROUPS) then
  begin
    Result := RETVAL_DATA_ERROR;
    Exit;
  end;

  nSelectors := get_bits(bd, 15);
  if nSelectors = 0 then
  begin
    Result := RETVAL_DATA_ERROR;
    Exit;
  end;

  for i := 0 to groupCount-1 do
    mtfSymbol[i] := i;

  for i := 0 to nSelectors-1 do
  begin
    j := 0;
    while get_bits(bd, 1) <> 0 do
    begin
      Inc(j);
      if j >= groupCount then
      begin
        Result := RETVAL_DATA_ERROR;
        Exit;
      end;
    end;

    uc := mtfSymbol[j];
    while j > 0 do
    begin
      mtfSymbol[j] := mtfSymbol[j-1];
      Dec(j);
    end;
    mtfSymbol[0] := uc;
    selectors[i] := uc;
  end;

  symCount := symTotal + 2;
  for j := 0 to groupCount-1 do
  begin
    hufGroup := @bd^.groups[j];

    t := get_bits(bd, 5) - 1;
    for i := 0 to symCount-1 do
    begin
      huffBitsReceived := False;  // Flag to track if Huffman bits were successfully received.
      while not huffBitsReceived do
      begin
        if Cardinal(t) > (MAX_HUFCODE_BITS - 1) then
        begin
          Result := RETVAL_DATA_ERROR;
          Exit;
        end;

        k := get_bits(bd, 2);
        if k < 2 then
        begin
          Inc(bd^.inbufBitCount);
          huffBitsReceived := True;  // Break the loop when bits are successfully received.
        end
        else
        begin
          t := t + (((k + 1) and 2) - 1);
        end;
      end;
      length[i] := t + 1;
    end;

    minLen := length[0];
    maxLen := length[0];
    for i := 1 to symCount-1 do
    begin
      if length[i] > maxLen then
        maxLen := length[i]
      else if length[i] < minLen then
        minLen := length[i];
    end;

    hufGroup^.minLen := minLen;
    hufGroup^.maxLen := maxLen;
    base := @hufGroup^.base[0] - 1;
    limit := @hufGroup^.limit[0] - 1;

    pp := 0;
    for i := minLen to maxLen do
    begin
      temp[i] := 0;
      limit[i] := 0;
      for t := 0 to symCount-1 do
        if length[t] = i then
        begin
          hufGroup^.permute[pp] := t;
          Inc(pp);
        end;
    end;

    for i := 0 to symCount-1 do
      Inc(temp[length[i]]);

    pp := 0;
    t := 0;
    for i := minLen to maxLen-1 do
    begin
      pp := pp + temp[i];
      limit[i] := (pp shl (maxLen - i)) - 1;
      pp := pp shl 1;
      base[i+1] := pp - (t + temp[i]);
      t := t + temp[i];
    end;
    limit[maxLen] := pp + temp[maxLen] - 1;
    base[minLen] := 0;
  end;

  for i := 0 to 255 do
  begin
    byteCount[i] := 0;
    mtfSymbol[i] := i;
  end;

  runPos := 0;
  dbufCount := 0;
  symCount := 0;
  selector := 0;

  while True do
  begin
    if symCount = 0 then
    begin
      symCount := GROUP_SIZE - 1;
      if selector >= nSelectors then
      begin
        Result := RETVAL_DATA_ERROR;
        Exit;
      end;
      hufGroup := @bd^.groups[selectors[selector]];
      Inc(selector);
      base := @hufGroup^.base[0] - 1;
      limit := @hufGroup^.limit[0] - 1;
    end;
    Dec(symCount);

    while bd^.inbufBitCount < hufGroup^.maxLen do
    begin
      if bd^.inbufPos = bd^.inbufCount then
      begin
        j := get_bits(bd, hufGroup^.maxLen);
        huffBitsReceived := True;  // Indicate Huffman bits are successfully received.
        break;
      end;
      bd^.inbufBits := (bd^.inbufBits shl 8) or bd^.inbuf[bd^.inbufPos];
      Inc(bd^.inbufPos);
      Inc(bd^.inbufBitCount, 8);
    end;

    if huffBitsReceived then
    begin
      Dec(bd^.inbufBitCount, hufGroup^.maxLen);
      j := (bd^.inbufBits shr bd^.inbufBitCount) and ((1 shl hufGroup^.maxLen) - 1);

      i := hufGroup^.minLen;
      while j > limit[i] do
        Inc(i);
      Inc(bd^.inbufBitCount, hufGroup^.maxLen - i);

      j := (j shr (hufGroup^.maxLen - i)) - base[i];
      if (i > hufGroup^.maxLen) or (j >= MAX_SYMBOLS) then
      begin
        Result := RETVAL_DATA_ERROR;
        Exit;
      end;
      nextSym := hufGroup^.permute[j];
    end;

    if Cardinal(nextSym) <= SYMBOL_RUNB then
    begin
      if runPos = 0 then
      begin
        runPos := 1;
        t := 0;
      end;
      t := t + (runPos shl nextSym);
      runPos := runPos shl 1;
      Continue;
    end;

    if runPos <> 0 then
    begin
      runPos := 0;
      if dbufCount + t >= dbufSize then
      begin
        Result := RETVAL_DATA_ERROR;
        Exit;
      end;

      uc := symToByte[mtfSymbol[0]];
      Inc(byteCount[uc], t);
      while t > 0 do
      begin
        dbuf[dbufCount] := uc;
        Inc(dbufCount);
        Dec(t);
      end;
    end;

    if nextSym > symTotal then
      Break;

    if dbufCount >= dbufSize then
    begin
      Result := RETVAL_DATA_ERROR;
      Exit;
    end;

    i := nextSym - 1;
    uc := mtfSymbol[i];
    while i > 0 do
    begin
      mtfSymbol[i] := mtfSymbol[i-1];
      Dec(i);
    end;
    mtfSymbol[0] := uc;
    uc := symToByte[uc];
    Inc(byteCount[uc]);
    dbuf[dbufCount] := uc;
    Inc(dbufCount);
  end;

  j := 0;
  for i := 0 to 255 do
  begin
    k := j + byteCount[i];
    byteCount[i] := j;
    j := k;
  end;

  for i := 0 to dbufCount-1 do
  begin
    uc := dbuf[i] and $ff;
    dbuf[byteCount[uc]] := dbuf[byteCount[uc]] or (i shl 8);
    Inc(byteCount[uc]);
  end;

  if dbufCount > 0 then
  begin
    if origPtr >= dbufCount then
    begin
      Result := RETVAL_DATA_ERROR;
      Exit;
    end;
    bd^.writePos := dbuf[origPtr];
    bd^.writeCurrent := bd^.writePos and $ff;
    bd^.writePos := bd^.writePos shr 8;
    bd^.writeRunCountdown := 5;
  end;
  bd^.writeCount := dbufCount;

  Result := RETVAL_OK;
end;

function read_bunzip(bd: Pbunzip_data; outbuf: PChar; len: Integer): Integer;
var
  dbuf: PCardinal;
  pos, current, previous, gotcount: Integer;
label
  decode_next_byte;
begin
  if bd^.writeCount < 0 then
  begin
    Result := bd^.writeCount;
    Exit;
  end;

  gotcount := 0;
  dbuf := bd^.dbuf;
  pos := bd^.writePos;
  current := bd^.writeCurrent;

  if bd^.writeCopies > 0 then
  begin
    Dec(bd^.writeCopies);
    while True do
    begin
      if gotcount >= len then
      begin
        bd^.writePos := pos;
        bd^.writeCurrent := current;
        Inc(bd^.writeCopies);
        Result := len;
        Exit;
      end;
      outbuf[gotcount] := Chr(current);
      Inc(gotcount);
      bd^.writeCRC := ((bd^.writeCRC shl 8) xor bd^.crc32Table[(bd^.writeCRC shr 24) xor current]);
      if bd^.writeCopies > 0 then
      begin
        Dec(bd^.writeCopies);
        Continue;
      end;

decode_next_byte:
      if bd^.writeCount = 0 then
        Break;
      Dec(bd^.writeCount);
      previous := current;
      pos := dbuf[pos];
      current := pos and $ff;
      pos := pos shr 8;
      Dec(bd^.writeRunCountdown);
      if bd^.writeRunCountdown <> 0 then
      begin
        if current <> previous then
          bd^.writeRunCountdown := 4;
      end
      else
      begin
        bd^.writeCopies := current;
        current := previous;
        bd^.writeRunCountdown := 5;
        if bd^.writeCopies = 0 then
          goto decode_next_byte;
        Dec(bd^.writeCopies);
      end;
    end;
    bd^.writeCRC := not bd^.writeCRC;
    bd^.totalCRC := ((bd^.totalCRC shl 1) or (bd^.totalCRC shr 31)) xor bd^.writeCRC;
    if bd^.writeCRC <> bd^.headerCRC then
    begin
      bd^.totalCRC := bd^.headerCRC + 1;
      Result := RETVAL_LAST_BLOCK;
      Exit;
    end;
  end;

  previous := get_next_block(bd);
  if previous <> 0 then
  begin
    bd^.writeCount := previous;
    if previous <> RETVAL_LAST_BLOCK then
      Result := previous
    else
      Result := gotcount;
    Exit;
  end;
  bd^.writeCRC := $ffffffff;
  pos := bd^.writePos;
  current := bd^.writeCurrent;
  goto decode_next_byte;
end;

function start_bunzip(var bdp: Pbunzip_data; in_fd: TFileStream; inbuf: PByte; len: Integer): Integer;
var
  bd: Pbunzip_data;
  i, j: Cardinal;
  c: Cardinal;
  BZh0: Cardinal;
begin
  BZh0 := (Ord('B') shl 24) + (Ord('Z') shl 16) + (Ord('h') shl 8) + Ord('0');

  i := SizeOf(Tbunzip_data);
  if in_fd <> nil then
    Inc(i, IOBUFF_SIZE);

  bd := GetMem(i);
  if bd = nil then
  begin
    Result := RETVAL_OUT_OF_MEMORY;
    Exit;
  end;
  FillChar(bd^, SizeOf(Tbunzip_data), 0);
  bdp := bd;

  bd^.in_fd := in_fd;
  if in_fd = nil then
  begin
    bd^.inbuf := inbuf;
    bd^.inbufCount := len;
  end
  else
    bd^.inbuf := PByte(bd) + SizeOf(Tbunzip_data);

  for i := 0 to 255 do
  begin
    c := i shl 24;
    for j := 8 downto 1 do
      if (c and $80000000) <> 0 then
        c := (c shl 1) xor $04c11db7
      else
        c := c shl 1;
    bd^.crc32Table[i] := c;
  end;

  i := setjmp(bd^.jmpbuf);
  if i <> 0 then
  begin
    Result := i;
    Exit;
  end;

  i := get_bits(bd, 32);
  if (i - BZh0 - 1) >= 9 then
  begin
    Result := RETVAL_NOT_BZIP_DATA;
    Exit;
  end;

  bd^.dbufSize := 100000 * (i - BZh0);
  bd^.dbuf := GetMem(bd^.dbufSize * SizeOf(Cardinal));
  if bd^.dbuf = nil then
  begin
    Result := RETVAL_OUT_OF_MEMORY;
    Exit;
  end;
  Result := RETVAL_OK;
end;

function BZ2DecompressStream(InStream, OutStream: TFileStream): Integer;
var
  outbuf: PChar;
  bd: Pbunzip_data;
  i: Integer;
begin
  outbuf := GetMem(IOBUFF_SIZE);
  if outbuf = nil then
  begin
    Result := RETVAL_OUT_OF_MEMORY;
    Exit;
  end;

  i := start_bunzip(bd, InStream, nil, 0);
  if i = RETVAL_OK then
  begin
    while True do
    begin
      i := read_bunzip(bd, outbuf, IOBUFF_SIZE);
      if i <= 0 then
        Break;
      if OutStream.Write(outbuf^, i) <> i then
      begin
        i := RETVAL_UNEXPECTED_OUTPUT_EOF;
        Break;
      end;
    end;
  end;

  if (i = RETVAL_LAST_BLOCK) and (bd^.headerCRC = bd^.totalCRC) then
    i := RETVAL_OK;

  if bd^.dbuf <> nil then
    FreeMem(bd^.dbuf);
  FreeMem(bd);
  FreeMem(outbuf);
  Result := i;
end;

end.

