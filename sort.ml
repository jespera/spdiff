let before a b = a <= b
let (-->) a b = before a b

let rec sort es = 
  let rec insert ds a = match ds with
  | [] -> [a]
  | b :: ds when a --> b -> a :: b :: ds
  | b :: ds -> b :: insert ds a
  in
  List.fold_left insert [] es
