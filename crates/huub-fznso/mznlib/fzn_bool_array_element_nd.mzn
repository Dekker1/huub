% As `fzn_int_array_element_nd.mzn`, for an array of Booleans.

include "fzn_bool_array_element.mzn";

predicate fzn_bool_array_element_nd(
  list of var bool: xs,
  list of int: offsets,
  list of int: sizes,
  list of var int: indices,
  var bool: value,
) =
  let {
    int: d = length(sizes);
    array [1..d] of int: stride = [product (e in i + 1..d) (sizes[e]) | i in 1..d];
  } in forall (i in 1..d) (indices[i] in offsets[i]..offsets[i] + sizes[i] - 1)
    /\ fzn_bool_array_element(
      xs,
      1,
      1 + sum (i in 1..d) (stride[i] * (indices[i] - offsets[i])),
      value,
    );
