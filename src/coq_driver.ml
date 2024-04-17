module Doption = struct
  let rep = "Gospel.Option"
end

module Dlist = struct
  let nil = "Coq.Lists.List.nil"
  let cons = "Coq.Lists.List.cons"
  let t = "Coq.Lists.List.list"
  let length = "LibListZ.length"
  let head = "Gospel.hd"
  let tl = "Gospel.tl"
  let app = "Coq.Lists.List.app"
  let mem = "Coq.Lists.List.mem"
  let remove = "Coq.Lists.List.remove"
  let singleton = "Gospel.singleton"
  let get = "Gospel.nth"
end

module Dmap = struct
  let update = "Gospel.update"
  let domain = "Gospel.domain"
end


module Dset = struct
  let cardinal = "TLC.LibSet.card_impl"
  let singleton = "TLC.LibSet.single_impl"
  let t = "TLC.LibSet.set"
  let add="Gospel.add_set"
  let remove="TLC.LibSet.remove_impl"
end

module Dz = struct
  let t = "Coq.Numbers.BinNums.Z"
  let ge = "TLC.LibOrder.ge"
  let gt = "TLC.LibOrder.gt"
  let le = "TLC.LibOrder.le"
  let lt = "TLC.LibOrder.lt"
  let rep = "Gospel.Int"
end

let eq = "Coq.Init.Logic.eq"
let word_size = "Gospel.word_size"


let ignore_list =
  List.map ((^) "Gospelstdlib.") [
      "Sequence.of_list";
      "List.to_sequence";
      "integer_of_int";
  ]

let type_mapping_list = [
    ("sequence", Dlist.t);
    ("integer", Dz.t);
    ("set", Dset.t);
  ]

let sequence_map = [
    ("empty", Dlist.nil);
    ("cons", Dlist.cons);
    ("hd", Dlist.head);
    ("tl", Dlist.tl);
    ("singleton", Dlist.singleton);
    ("mem", Dlist.mem);
    ("remove", Dlist.remove);
    ("length", Dlist.length);    
  ]

let set_map = [    
    "cardinal", Dset.cardinal;
    "singleton", Dset.singleton;
    "add", Dset.add;
    "remove", Dset.remove;
  ]

let map_map = [
    "domain", Dmap.domain;
  ]

let sys_map = [
    "word_size", word_size;
  ]

let append s =
  List.map (fun (k, v) -> s ^ "." ^ k, v)

let id_mapping_list =
  [
    ("infix =", eq);
    ("infix ++", Dlist.app);
    ("mixfix [_]", Dlist.get);
    ("mixfix [->]", Dmap.update);
    "infix >=", Dz.ge;
    "infix >", Dz.gt;
    "infix <=", Dz.le;
    "infix <", Dz.lt;
    "Option", Doption.rep;
    "Int", Dz.rep;
  ] @ (append "Sequence" sequence_map)
  @ (append "Set" set_map)
  @ (append "Map" map_map)
  @ (append "Sys" sys_map)
