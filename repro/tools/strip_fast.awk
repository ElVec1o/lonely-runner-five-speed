# strip_fast.awk : like repro_four/tools/strip.awk (block comments nest, line comments dropped) with a fast path for lines that contain no
# comment marker outside an open block comment (the huge generated data lines).  Prints "file:line:code" for non-blank remaining code.
BEGIN { depth = 0 }
FNR == 1 { depth = 0 }
{
  line = $0
  if (depth == 0 && index(line, "/-") == 0 && index(line, "--") == 0) { if (line ~ /[^ \t]/) print FILENAME ":" FNR ":" line; next }
  out = ""; i = 1; n = length(line)
  while (i <= n) {
    two = substr(line, i, 2)
    if (depth > 0) {
      if (two == "/-") { depth++; i += 2 } else if (two == "-/") { depth--; i += 2 } else i++
    } else {
      if (two == "/-") { depth++; i += 2 } else if (two == "--") { break } else { out = out substr(line, i, 1); i++ }
    }
  }
  if (out ~ /[^ \t]/) print FILENAME ":" FNR ":" out
}
