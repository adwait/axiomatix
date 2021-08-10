
let outfile = ref stdout
let printfFlush x y = Printf.fprintf !outfile "%s" y; flush !outfile; x