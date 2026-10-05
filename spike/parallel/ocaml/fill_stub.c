#include <caml/mlvalues.h>
#include <caml/memory.h>
#include <caml/bigarray.h>
#include "Spike_FillHalves.h"
#include "thread_probe.h"

value spike_fill_halves(value ba)
{
  CAMLparam1(ba);
  Spike_FillHalves_fill_halves((uint64_t *)Caml_ba_data_val(ba), Caml_ba_array_val(ba)->dim[0]);
  CAMLreturn(Val_unit);
}

value spike_thread_probe_fill(value ba)
{
  CAMLparam1(ba);
  bool distinct = thread_probe_fill((uint64_t *)Caml_ba_data_val(ba), Caml_ba_array_val(ba)->dim[0]);
  CAMLreturn(Val_bool(distinct));
}
