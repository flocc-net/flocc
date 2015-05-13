#ifndef CARTTOPS_H
#define CARTTOPS_H

#include <vector>
#include <algorithm>
#include <iostream>

using namespace std;

namespace flocc {

// return prime factors of n
vector<int> primeFactors(int n) {
  vector<int> res;
  int z = 2;
  while (z*z <= n) {
    if (n % z == 0) {
      res.push_back(z);
      n /= z;
    } else {
      z++;
    }
  }
  if (n > 1) res.push_back(n);
  return res;
}

// return ndim dim sizes which multiply up to N
// tries to keep dim sizes as equal as possible
vector<int> calcDimSizes(int N, int ndims) {
  // check at least 1 dim
  if (ndims <= 0) {
    cerr << "calcDimSizes: ndims must be >= 1\n";
    throw 1; 
  }

  // get prime factors of N
  vector<int> res = primeFactors(N);
  sort(res.begin(), res.end());

  // modify until num factors = ndims
  while (res.size() > ndims) {
    // combine smallest factors
    int v = res[0];
    res.erase(res.begin());
    res[0] *= v;
    sort(res.begin(), res.end());
  }
  while (res.size() < ndims) {
    // add dims of length 1
    res.push_back(1);
  }
  sort(res.begin(), res.end());

  return res;
} 

// count the number of times val occurs in vec
int countInVec(vector<int> vec, int val) {
  int count = 0;
  for (vector<int>::iterator it = vec.begin(); 
       it != vec.end(); it++) 
  {
    if (*it == val) count++;
  }
  return count;
}

// explores (smaller) neighbors of N, to find one which gives
// the most non-one dim sizes.q
/*vector<int> findBestDims(int N, int ndims) {
  // start with N itself
  vector<int> curBestVec = calcDimSizes(N, ndims);
  int curBestCount = countInVec(curBestVec, 1);

  // try 4 immediate neighbours
  for (int curN = N-4; curN < N; curN++) {
    vector<int> sizes = calcDimSizes(curN, ndims);
    int numOnes = countInVec(sizes, 1);
    if (numOnes < curBestCount) {
      curBestCount = numOnes;
      curBestVec = sizes;
    }
  }

  return curBestVec;
}*/

// explores (smaller) neighbors of N, to find one has the
// smallest difference between the smallest and largest
// sizes.
vector<int> findBestDims(int N, int ndims) {
  // start with N itself
  vector<int> curBestVec = calcDimSizes(N, ndims);
  int curBestDif = curBestVec.back() - curBestVec.front();

  // try 4 immediate neighbours
  for (int curN = N-4; curN < N; curN++) {
    vector<int> sizes = calcDimSizes(curN, ndims);
    int diff = sizes.back() - sizes.front();
    if (diff < curBestDif) {
      curBestDif = diff;
      curBestVec = sizes;
    }
  }

  return curBestVec;
}


// display a vector of ints
void showVec(vector<int> v) {
  for (vector<int>::iterator it = v.begin(); 
       it != v.end(); it++) 
  {
    cout << *it << ", ";
  }
}

int mulVec(vector<int> v) {
  int res = 1;
  for (vector<int>::iterator it = v.begin(); 
       it != v.end(); it++) 
  {
    res *= *it;
  }
  return res;
}

}

/*int main(int argc, char** argv) {
  // calc dim sizes for different number of nodes and ndims
  for (int N = 1; N < 121; N++) {
    cout << "N: " << N << "\n";
    for (int ndims = 1; ndims < 6; ndims++) {
      cout << "    ndims: " << ndims << ": ";
      vector<int> sizes1 = findBestDims2(N, ndims);
      showVec(sizes1);
      cout << " = " << mulVec(sizes1);
      vector<int> sizes2 = calcDimSizes(N, ndims);
      cout << " instead of ";
      showVec(sizes2);
      cout << "\n";
    } 
  }
  
  return 0;
}*/

#endif


