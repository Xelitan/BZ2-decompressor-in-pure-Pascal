# BZ2-decompressor-in-pure-Pascal
BZ2 decompressor in pure Pascal

```
var F,P: TFileStream;
begin
   F := TFileStream.Create('test.bz2', fmOpenRead);
   P := TFileStream.Create('test.txt', fmCreate);
   BZ2DecompressStream(F, P);

   F.Free;
   P.FRee;
end;
```
