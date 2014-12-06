#include <iostream>
#include <cstdio>
#include "engine/trail.h"

int main(int argc, char** argv)
{
  Trail t;

  Trailed<int> i(&t, 0);

  i = 7;

  fprintf(stdout, "Level: %d\n", t.level());

  fprintf(stdout, "%d <- %d <- %d\n", (int) i, i.prev_val(), i.prev_level_val());
  t.commit();
  fprintf(stdout, "%d <- %d <- %d\n", (int) i, i.prev_val(), i.prev_level_val());
  t.push_level();
  fprintf(stdout, "%d <- %d <- %d\n", (int) i, i.prev_val(), i.prev_level_val());
  
  i = 18;
  fprintf(stdout, "%d <- %d <- %d\n", (int) i, i.prev_val(), i.prev_level_val());
  t.commit();
  fprintf(stdout, "%d <- %d <- %d\n", (int) i, i.prev_val(), i.prev_level_val());

  t.restore_level();
  fprintf(stdout, "%d <- %d <- %d\n", (int) i, i.prev_val(), i.prev_level_val());
  return 0;
}
