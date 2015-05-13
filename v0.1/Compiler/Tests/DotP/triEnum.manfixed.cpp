#include "header.h"


// Global cartesian communicator
static const int ndims = 1;
static const int maxNodesPerDim = 4096;
static std::vector<int> dimSizes;
static MPI::Cartcomm cartComm;
static int coordRanks[maxNodesPerDim];
static int thisCoord[ndims];
static int thisRank, Nproc, rootRank;


typedef struct struct11 {
int v0;
int v1;
bool operator<(const struct11& b) const {
  return (v0 < b.v0) || ((v0 == b.v0) && ((v1 < b.v1)));
}
bool operator>=(const struct11& b) const {
  return !((v0 < b.v0) || ((v0 == b.v0) && ((v1 < b.v1))));
}
inline bool operator==(const struct11& b) const {
  return (v0 == b.v0) && (v1 == b.v1);
}
inline bool operator!=(const struct11& b) const {
  return !((v0 == b.v0) && (v1 == b.v1));
}
} struct11;
void printVal(const struct11& v) {
printVal("(");
printVal(v.v0);
printVal(", ");
printVal(v.v1);
printVal(")");

}
 namespace flocc {
   template<>
   struct hasher<struct11> {
   public:
       static inline hash_t hash(struct11 const& v) {
           hash_t seed = 0;
             hash_combine<int>(seed, v.v0);
  hash_combine<int>(seed, v.v1);
  
           return seed;
        }
   };
 }
struct eqstruct11 {
inline bool operator()(const struct11& a, const struct11& b) const {
  return (a.v0 == b.v0) && (a.v1 == b.v1);
}
};


typedef struct struct10 {
struct11 v0;
bool operator<(const struct10& b) const {
  return (v0.v0 < b.v0.v0) || ((v0.v0 == b.v0.v0) && (v0.v1 < b.v0.v1) || ((v0.v1 == b.v0.v1) && (0)));
}
bool operator>=(const struct10& b) const {
  return !((v0.v0 < b.v0.v0) || ((v0.v0 == b.v0.v0) && (v0.v1 < b.v0.v1) || ((v0.v1 == b.v0.v1) && (0))));
}
inline bool operator==(const struct10& b) const {
  return (v0.v0 == b.v0.v0) && (v0.v1 == b.v0.v1) && 1;
}
inline bool operator!=(const struct10& b) const {
  return !((v0.v0 == b.v0.v0) && (v0.v1 == b.v0.v1) && 1);
}
} struct10;
void printVal(const struct10& v) {
printVal("(");
printVal("(");
printVal(v.v0.v0);
printVal(", ");
printVal(v.v0.v1);
printVal(")");
printVal(", ");
printVal(")");

}
 namespace flocc {
   template<>
   struct hasher<struct10> {
   public:
       static inline hash_t hash(struct10 const& v) {
           hash_t seed = 0;
             seed = hasher<struct11>::hash(v.v0);
  
           return seed;
        }
   };
 }
struct eqstruct10 {
inline bool operator()(const struct10& a, const struct10& b) const {
  return (a.v0.v0 == b.v0.v0) && (a.v0.v1 == b.v0.v1) && 1;
}
};


 namespace flocc {
   struct fun_class_12 {
   public:
       inline static char run(struct10 v13) {
           ;
             // v7052 = NULL
  ;
           return 0; // null value, is 0 char:  v14;
        }
   };
 }
 namespace flocc {
   struct fun_class_7064 {
   public:
       inline static struct11 run(struct10 v7065) {
             struct11 v7066;
  ;
             // TupNd assignment
    v7066.v0 = v7065.v0.v0; //(Lf:(Int )) = (Lf:(Int ))
    v7066.v1 = v7065.v0.v1; //(Lf:(Int )) = (Lf:(Int ))
    
  ;
           return  v7066;
        }
   };
 }
 namespace flocc {
   struct fun_class_7075 {
   public:
       inline static int run(struct10 v7076) {
             int v7077;
  ;
             // TupAccNd assignment
    v7077 = v7076.v0.v0; //(Lf:(Int )) = (Lf:(Int ))
    
  ;
           return  v7077;
        }
   };
 }
typedef struct struct7100 {
struct11 v0;
struct11 v1;
bool operator<(const struct7100& b) const {
  return (v0.v0 < b.v0.v0) || ((v0.v0 == b.v0.v0) && (v0.v1 < b.v0.v1) || ((v0.v1 == b.v0.v1) && (v1.v0 < b.v1.v0) || ((v1.v0 == b.v1.v0) && ((v1.v1 < b.v1.v1)))));
}
bool operator>=(const struct7100& b) const {
  return !((v0.v0 < b.v0.v0) || ((v0.v0 == b.v0.v0) && (v0.v1 < b.v0.v1) || ((v0.v1 == b.v0.v1) && (v1.v0 < b.v1.v0) || ((v1.v0 == b.v1.v0) && ((v1.v1 < b.v1.v1))))));
}
inline bool operator==(const struct7100& b) const {
  return (v0.v0 == b.v0.v0) && (v0.v1 == b.v0.v1) && (v1.v0 == b.v1.v0) && (v1.v1 == b.v1.v1);
}
inline bool operator!=(const struct7100& b) const {
  return !((v0.v0 == b.v0.v0) && (v0.v1 == b.v0.v1) && (v1.v0 == b.v1.v0) && (v1.v1 == b.v1.v1));
}
} struct7100;
void printVal(const struct7100& v) {
printVal("(");
printVal("(");
printVal(v.v0.v0);
printVal(", ");
printVal(v.v0.v1);
printVal(")");
printVal(", ");
printVal("(");
printVal(v.v1.v0);
printVal(", ");
printVal(v.v1.v1);
printVal(")");
printVal(")");

}
 namespace flocc {
   template<>
   struct hasher<struct7100> {
   public:
       static inline hash_t hash(struct7100 const& v) {
           hash_t seed = 0;
             hash_combine<struct11>(seed, v.v0);
  hash_combine<struct11>(seed, v.v1);
  
           return seed;
        }
   };
 }
struct eqstruct7100 {
inline bool operator()(const struct7100& a, const struct7100& b) const {
  return (a.v0.v0 == b.v0.v0) && (a.v0.v1 == b.v0.v1) && (a.v1.v0 == b.v1.v0) && (a.v1.v1 == b.v1.v1);
}
};


typedef struct struct7101 {
bool operator<(const struct7101& b) const {
  return 0 || (1 && (0));
}
bool operator>=(const struct7101& b) const {
  return !(0 || (1 && (0)));
}
inline bool operator==(const struct7101& b) const {
  return 1 && 1;
}
inline bool operator!=(const struct7101& b) const {
  return !(1 && 1);
}
} struct7101;
void printVal(const struct7101& v) {
printVal("(");
printVal(", ");
printVal(")");

}
 namespace flocc {
   template<>
   struct hasher<struct7101> {
   public:
       static inline hash_t hash(struct7101 const& v) {
           hash_t seed = 0;
           
           return seed;
        }
   };
 }
struct eqstruct7101 {
inline bool operator()(const struct7101& a, const struct7101& b) const {
  return 1 && 1;
}
};


typedef struct struct7099 {
struct7100 v0;
struct7101 v1;
bool operator<(const struct7099& b) const {
#if 0
  return (v0.v0.v0 < b.v0.v0.v0)  || (
                ((v0.v0.v0 == b.v0.v0.v0) && (v0.v0.v1 < b.v0.v0.v1)) || (
                        ((v0.v0.v1 == b.v0.v0.v1) && (v0.v1.v0 < b.v0.v1.v0)) || (
                                     ((v0.v1.v0 == b.v0.v1.v0) && (v0.v1.v1 < b.v0.v1.v1)) || (
                                              ((v0.v1.v1 == b.v0.v1.v1) && 0) || (1 && (0))))));
#endif
  if (v0.v0.v0 < b.v0.v0.v0)
    return true;
  else if (v0.v0.v0 > b.v0.v0.v0)
    return false;

  if (v0.v0.v1 < b.v0.v0.v1)
    return true;
  else if (v0.v0.v1 > b.v0.v0.v1)
    return false;

  if (v0.v1.v0 < b.v0.v1.v0)
    return true;
  else if (v0.v1.v0 > b.v0.v1.v0)
    return false;

  if (v0.v1.v1 < b.v0.v1.v1)
    return true;
  else if (v0.v1.v1 > b.v0.v1.v1)
    return false;

  return false;

}
bool operator>=(const struct7099& b) const {
  return !((v0.v0.v0 < b.v0.v0.v0) || ((v0.v0.v0 == b.v0.v0.v0) && (v0.v0.v1 < b.v0.v0.v1) || ((v0.v0.v1 == b.v0.v0.v1) && (v0.v1.v0 < b.v0.v1.v0) || ((v0.v1.v0 == b.v0.v1.v0) && (v0.v1.v1 < b.v0.v1.v1) || ((v0.v1.v1 == b.v0.v1.v1) && 0 || (1 && (0)))))));
}
inline bool operator==(const struct7099& b) const {
  return (v0.v0.v0 == b.v0.v0.v0) && (v0.v0.v1 == b.v0.v0.v1) && (v0.v1.v0 == b.v0.v1.v0) && (v0.v1.v1 == b.v0.v1.v1) && 1 && 1;
}
inline bool operator!=(const struct7099& b) const {
  return !((v0.v0.v0 == b.v0.v0.v0) && (v0.v0.v1 == b.v0.v0.v1) && (v0.v1.v0 == b.v0.v1.v0) && (v0.v1.v1 == b.v0.v1.v1) && 1 && 1);
}
} struct7099;
void printVal(const struct7099& v) {
printVal("(");
printVal("(");
printVal("(");
printVal(v.v0.v0.v0);
printVal(", ");
printVal(v.v0.v0.v1);
printVal(")");
printVal(", ");
printVal("(");
printVal(v.v0.v1.v0);
printVal(", ");
printVal(v.v0.v1.v1);
printVal(")");
printVal(")");
printVal(", ");
printVal("(");
printVal(", ");
printVal(")");
printVal(")");

}
 namespace flocc {
   template<>
   struct hasher<struct7099> {
   public:
       static inline hash_t hash(struct7099 const& v) {
           hash_t seed = 0;
             hash_combine<struct7100>(seed, v.v0);
  hash_combine<struct7101>(seed, v.v1);
  
           return seed;
        }
   };
 }
struct eqstruct7099 {
inline bool operator()(const struct7099& a, const struct7099& b) const {
  return (a.v0.v0.v0 == b.v0.v0.v0) && (a.v0.v0.v1 == b.v0.v0.v1) && (a.v0.v1.v0 == b.v0.v1.v0) && (a.v0.v1.v1 == b.v0.v1.v1) && 1 && 1;
}
};


 namespace flocc {
   struct fun_class_7102 {
   public:
       inline static struct11 run(struct7099 v7103) {
             struct11 v7104;
  ;
             // TupNd assignment
    v7104.v0 = v7103.v0.v0.v0; //(Lf:(Int )) = (Lf:(Int ))
    v7104.v1 = v7103.v0.v1.v0; //(Lf:(Int )) = (Lf:(Int ))
    
  ;
           return  v7104;
        }
   };
 }
 namespace flocc {
   struct fun_class_7137 {
   public:
       inline static struct11 run(struct10 v7138) {
             struct11 v7139;
  ;
             // TupAccNd assignment
    v7139 = v7138.v0; //((Lf:(Int )), (Lf:(Int ))) = ((Lf:(Int )), (Lf:(Int )))
    
  ;
           return  v7139;
        }
   };
 }
 // user def reduction function
  void userFun7166(const void* invec, void *inoutvec, int len, const MPI::Datatype& datatype) {
   const int* in = (const int*)invec;
   int* out = (int*)inoutvec;
   // TODO: WHEN SENDING PROPER DATATYPE, CHANGE (len / sizeof(int)) to len!
   for (int i = 0; i < (len / sizeof(int)); i++) {
     int val2 = out[i];
       out[i] = in[i] + val2;
  
  }
 }

MPI::Op v7171;



void run() {
// Init global cartesian topology
thisRank = MPI::COMM_WORLD.Get_rank();
Nproc = MPI::COMM_WORLD.Get_size();
dimSizes = flocc::findBestDims(Nproc, ndims);

bool periods[ndims]; for (int i = 0; i < ndims; i++) periods[i] = false;
cartComm = MPI::COMM_WORLD.Create_cart(ndims, &dimSizes.front(), periods, true);

{
 int coord[ndims];
for (coord[0] = 0; coord[0] < dimSizes[0]; coord[0]++) {
coordRanks[coord[0]] = cartComm.Get_cart_rank(coord);
}

}
rootRank = coordRanks[0];
v7171.Init(&userFun7166, true);

// v1 = NULL
// BEGIN loadIntPairDStream
#ifdef DEBUG
std::cerr << thisRank << ") BEGIN loadIntPairDStream\n";
#endif
    // BEGIN dStreamToDVecMap init
      struct10 v9;
        boost::shared_ptr<flocc::vecmap<struct10, struct11, char, flocc::fun_class_12 > > v7053(new flocc::vecmap<struct10, struct11, char, flocc::fun_class_12 >);
        flocc::reparter<struct10, flocc::vecmap<struct10, struct11, char, flocc::fun_class_12 > > v7054(&(cartComm), v7053);
      
    // END dStreamToDVecMap init
    
if (true) {
int v4, v5;
for (int v2 = 0; v2 < 1024*1024/Nproc; v2++) {
  v4 = rand() % 1024; v5 = rand() % 1024;
    // BEGIN mapDStream2 consume:
    int v6;
    int v7;
        bool v7195;
      v7195 = v4 < v5;
    // ifFun
    
    if (v7195) {
      // v7202 = NULL
      // TupNd assignment
        v6 = v4; //(Lf:(Int )) = (Lf:(Int ))
        v7 = v5; //(Lf:(Int )) = (Lf:(Int ))
        
      
    } else {
      // v7208 = NULL
      // TupNd assignment
        v6 = v5; //(Lf:(Int )) = (Lf:(Int ))
        v7 = v4; //(Lf:(Int )) = (Lf:(Int ))
        
      
    }
    
    // BEGIN dStreamToDVecMap consume
      v9.v0.v0 = v6; //(Lf:(Int )) = (Lf:(Int ))
      v9.v0.v1 = v7; //(Lf:(Int )) = (Lf:(Int ))
      
      int v7055;
      int v7056;
      
      // TupAccNd assignment
        v7055 = v6; //(Lf:(Int )) = (Lf:(Int ))
        v7056 = v7; //(Lf:(Int )) = (Lf:(Int ))
        
      
      int v7061;
      
      int hash7062 = 0;
        struct11 hashIn7063;
          hashIn7063.v0 = v7055; //(Lf:(Int )) = (Lf:(Int ))
        hashIn7063.v1 = v7056; //(Lf:(Int )) = (Lf:(Int ))
        
      hash7062 = flocc::hasher<struct11>::hash(hashIn7063);
      hash7062 = (unsigned int)hash7062 % dimSizes[0];
      mpiAssert(hash7062 >= 0 && hash7062 < dimSizes[0], "varToNodeRank: coord hash7062 out of range.");
      v7061 = coordRanks[hash7062];
      mpiAssert(v7061 >= 0 && v7061 < cartComm/* WARNING CHANGE TO USE SUB CARTS TOO */.Get_size(), "varToNodeRank: rank v7061 out of range.");
      
    v7054.push_back(v7061, v9);
    //END dStreamToDVecMap consume
    
  // END mapDStream2 consume
  
}
}
    // BEGIN dStreamToDVecMap fin
    v7054.finish();
    // END dStreamToDVecMap fin
    
// END loadIntPairDStream
#ifdef DEBUG
std::cerr << thisRank << ") END loadIntPairDStream\n";
#endif
// BEGIN sortDVecMap
#ifdef DEBUG
std::cerr << thisRank << ") BEGIN sortDVecMap\n";
#endif
  boost::shared_ptr<flocc::vecmap<struct10, struct11, struct11, flocc::fun_class_7064 > > v7074(new flocc::vecmap<struct10, struct11, struct11, flocc::fun_class_7064 >);
  
 // sort sec key type: ((Lf:(Int )), (Lf:(Int )))
if (true) { v7074->assign(v7053); }
// END sortDVecMap
#ifdef DEBUG
std::cerr << thisRank << ") END sortDVecMap\n";
#endif
// BEGIN allPairsDVecMap
#ifdef DEBUG
std::cerr << thisRank << ") BEGIN allPairsDVecMap\n";
#endif
  // BEGIN dStreamToDVecMap init
    struct7099 v7098;
      boost::shared_ptr<flocc::vecmap<struct7099, struct7100, struct11, flocc::fun_class_7102 > > v7118(new flocc::vecmap<struct7099, struct7100, struct11, flocc::fun_class_7102 >);
      flocc::reparter<struct7099, flocc::vecmap<struct7099, struct7100, struct11, flocc::fun_class_7102 > > v7119(&(cartComm), v7118);
    
  // END dStreamToDVecMap init
  
if (true) {
  flocc::vecmap<struct10, struct11, struct11, flocc::fun_class_7064 >::const_iterator v7084(v7074->cbegin());
    flocc::vecmap<struct10, struct11, struct11, flocc::fun_class_7064 >::const_iterator v7085(v7074->cbegin());
    flocc::vecmap<struct10, struct11, struct11, flocc::fun_class_7064 >::const_iterator v7086(v7074->cbegin());
    flocc::vecmap<struct10, struct11, struct11, flocc::fun_class_7064 >::const_iterator v7087(v7074->cend());
    int v7088;
  int v7089;
  
while (v7084 != v7087) {
    // TupAccNd assignment
    v7088 = v7084->v0.v0; //(Lf:(Int )) = (Lf:(Int ))
    
   // (Lf:(Int ))
  v7086 = v7074->findSecEnd<int, flocc::fun_class_7075 >(v7084, v7088);
  while (v7084 != v7086) {
    v7085 = v7084; v7085++;
    while (v7085 != v7086) {
        // BEGIN dStreamToDVecMap consume
    v7098.v0.v0 = v7084->v0; //((Lf:(Int )), (Lf:(Int ))) = ((Lf:(Int )), (Lf:(Int )))
    v7098.v0.v1 = v7085->v0; //((Lf:(Int )), (Lf:(Int ))) = ((Lf:(Int )), (Lf:(Int )))
    
    int v7120;
    int v7121;
    int v7122;
    int v7123;
    
    // TupAccNd assignment
      v7120 = v7084->v0.v0; //(Lf:(Int )) = (Lf:(Int ))
      v7121 = v7084->v0.v1; //(Lf:(Int )) = (Lf:(Int ))
      v7122 = v7085->v0.v0; //(Lf:(Int )) = (Lf:(Int ))
      v7123 = v7085->v0.v1; //(Lf:(Int )) = (Lf:(Int ))
      
    
    int v7128;
    
    int hash7129 = 0;
      struct7100 hashIn7130;
        hashIn7130.v0.v0 = v7120; //(Lf:(Int )) = (Lf:(Int ))
      hashIn7130.v0.v1 = v7121; //(Lf:(Int )) = (Lf:(Int ))
      hashIn7130.v1.v0 = v7122; //(Lf:(Int )) = (Lf:(Int ))
      hashIn7130.v1.v1 = v7123; //(Lf:(Int )) = (Lf:(Int ))
      
    hash7129 = flocc::hasher<struct7100>::hash(hashIn7130);
    hash7129 = (unsigned int)hash7129 % dimSizes[0];
    mpiAssert(hash7129 >= 0 && hash7129 < dimSizes[0], "varToNodeRank: coord hash7129 out of range.");
    v7128 = coordRanks[hash7129];
    mpiAssert(v7128 >= 0 && v7128 < cartComm/* WARNING CHANGE TO USE SUB CARTS TOO */.Get_size(), "varToNodeRank: rank v7128 out of range.");
    
  v7119.push_back(v7128, v7098);
  //END dStreamToDVecMap consume
  
      v7085++;
    }
    v7084++;
  }
}}
// END allPairsDVecMap
#ifdef DEBUG
std::cerr << thisRank << ") END allPairsDVecMap\n";
#endif
// BEGIN dVecMapToDStreamLocal
#ifdef DEBUG
std::cerr << thisRank << ") BEGIN dVecMapToDStreamLocal\n";
#endif
  // BEGIN eqJoinDStreamDVecMap init
      // BEGIN reduceDStream init
        int v7156;
          int v7157;
        int v7158;
        
      // END reduceDStream init
        flocc::vecmap<struct10, struct11, struct11, flocc::fun_class_7064 >::const_iterator v7133;
      flocc::vecmap<struct10, struct11, struct11, flocc::fun_class_7064 >::const_iterator v7134(v7074->cend());
      struct11 v7135;
    struct11 v7136;
    
  // END eqJoinDStreamDVecMap init
  
if (true) {
  flocc::vecmap<struct7099, struct7100, struct11, flocc::fun_class_7102 >::const_iterator v7131(v7118->cbegin());
    flocc::vecmap<struct7099, struct7100, struct11, flocc::fun_class_7102 >::const_iterator v7132(v7118->cend());
  
for (; v7131 != v7132; v7131++) {
    // BEGIN eqJoinDStreamDVecMap consume
    // TupAccNd assignment
      v7135 = v7131->v0.v1; //((Lf:(Int )), (Lf:(Int ))) = ((Lf:(Int )), (Lf:(Int )))
      
     // get key of input stream
    v7136 = v7135; //((Lf:(Int )), (Lf:(Int ))) = ((Lf:(Int )), (Lf:(Int )))
     // copy key1 to key2 so loop pred will match on first iteration
  v7133 = v7074->findSecBegin<struct11, flocc::fun_class_7137 >(v7135); // find first matching value in vecmap
  while (v7133 != v7134 && v7135 == v7136) { // loop while keys match
      // BEGIN mapDStream2 consume:
      int v7152;
      int v7153;
      int v7154;
        // v7221 = NULL
      // TupNd assignment
        v7152 = v7131->v0.v0.v0; //(Lf:(Int )) = (Lf:(Int ))
        v7153 = v7133->v0.v0; //(Lf:(Int )) = (Lf:(Int ))
        v7154 = v7133->v0.v1; //(Lf:(Int )) = (Lf:(Int ))
        
      
      // BEGIN reduceDStream consume
        v7156 = 1;
          v7157 = v7156 + v7158;
          v7158 = v7157; //(Lf:(Int )) = (Lf:(Int ))
        
      // END reduceDStream consume
      
    // END mapDStream2 consume
    
    v7133++;
      // TupAccNd assignment
      v7136 = v7133->v0; //((Lf:(Int )), (Lf:(Int ))) = ((Lf:(Int )), (Lf:(Int )))
      
    
  }
  // END eqJoinDStreamDVecMap consume
  
}
}
      // BEGIN reduceDStream fin
      if (true) {
        cartComm.Allreduce(&v7158, &v7156, sizeof(int), MPI_PACKED, v7171);
      }
      if (cartComm != cartComm) {
        cartComm.Bcast(&v7156, sizeof(int), MPI_PACKED, rootRank);
      }
      // END reduceDStream fin
      
// END dVecMapToDStreamLocal
#ifdef DEBUG
std::cerr << thisRank << ") END dVecMapToDStreamLocal\n";
#endif
// BEGIN printInt
#ifdef DEBUG
std::cerr << thisRank << ") BEGIN printInt\n";
#endif
if (thisRank == rootRank) std::cout << v7156;
// END printInt
#ifdef DEBUG
std::cerr << thisRank << ") END printInt\n";
#endif
// No stream called 'final' found in output streams.
}


int main(int argc, char** argv) {
  MPI::Init(argc, argv);
  run();
  MPI::Finalize();
  return 0;
}
//



