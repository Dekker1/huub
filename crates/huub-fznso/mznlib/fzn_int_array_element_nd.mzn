% Huub has no k-dimensional element propagator, and the registry's identifier
% promises every number of dimensions, so it is left undeclared and overridden
% here: the row-major index is one linear sum, and what is left is the
% one-dimensional element, which Huub declares.
%
% Each index is kept inside its own dimension. The flat index alone would accept
% an index past the end of one dimension that the next one makes up for.
%
% Every identifier below is a registry name Huub declares, so nothing here is
% rewritten back onto this predicate.

include "fzn_int_array_element.mzn";

predicate fzn_int_array_element_nd(
  list of var int: xs,
  list of int: offsets,
  list of int: sizes,
  list of var int: indices,
  var int: value,
) =
  let {
    int: d = length(sizes);
    array [1..d] of int: stride = [product (e in i + 1..d) (sizes[e]) | i in 1..d];
  } in forall (i in 1..d) (indices[i] in offsets[i]..offsets[i] + sizes[i] - 1)
    /\ fzn_int_array_element(
      xs,
      1,
      1 + sum (i in 1..d) (stride[i] * (indices[i] - offsets[i])),
      value,
    );
