typedef struct L4
{
  int l4_i1;
  int l4_i2;
} L4;

typedef struct L3_inner_struct
{
  int il3_ia[4];
  int il3_i1;
  int il3_i2;
} L3_IS;

typedef struct L3
{
  int l3_i1;
  int l3_ia[4];
  L3_IS l3_is;
  char l3_ca[5];
  long l3_l;
  L4 *l3_l4p;
  int l3_i2;
  int same_id_i;
  char l3_vla[0]; // variable-length array
} L3;

typedef struct L3o
{
  int same_id_i;
} L3o;

typedef struct L2
{
  int l2_i1;
  int l2_i2;
  int l2_bf : 3;
  volatile int l2_vi;
  L3 *l2_l3p;
  L3o *l2_l3op;

  union
  {
    char l2u_c;
    int l2u_i;
    float l2u_f;
  } l2u;
} L2;

/* The level 1 data structure of array */
typedef struct L1
{
  int l1_i1;
  L2 *l1_l2p;
} L1;

/* The level 1 data structure of list, i.e. list node.  */
typedef struct Node {
    L2 *l1_l2p;
    struct Node *next;
    char l1_c1;
} Node;
