#include<cstdio>
#include<cstring>
#include<iostream>
#include<fstream>
#include<cstdlib>
#include<vector>
#include<set>
#include<map>
#include<queue>
#include<algorithm>

//#include<ctime>
#include<sstream>
#include<chrono>
#include <boost/thread/thread.hpp>
#include <boost/bind.hpp>
#include <unordered_map>
#include<iterator>
#include<cmath>
#include "Semaphore.h"

using namespace std;
using namespace chrono;


/************************************************************************************************
 * @brief Please re-set PARAMETERs below if the graph is changed.
 * @param sm The number of threads on index contraction.
 * @param sm2 The number of threads on propagation.
 * @param sm3 The number of threads on small trees index construction.
 * @param ism1 Set its value as the same as <sm>
 * @param ism2 Set its value as the same as <sm2>
 * @param fn The number of partitions (re-set it if the number of partitions is changed).
 * @param All_v The number of vertices in the road network.
 * @param fullspace The total number of dimensions of the road network.
 * @param subgraphBound The path of the folder: sampleBoundData/sampleBoundData_SubBound.
 *      ~ NOTE:It needs to save the boundary vertices in every partition).
 * @param sub_bound_skylines The path of the folder: sampleBoundData/sampleBoundData_2DSky.
 *      ~ NOTE:It needs to save the skyline paths from boundary vertices to boundary vertices.
 *             The folder sampleBoundData only provides the skyline paths in all the 2d subspaces, 
 *             Pleass use the complete skyline paths for testing the real performance.
 * @author Ziyi Liu
 * @date March 2022
 ************************************************************************************************/

//
//##################<Control Panel>#####################################################
int ism1 = 10;                                                                                                                                  
int ism2 = 30;   																																																							
Semaphore* sm = new Semaphore(30);                       																						
Semaphore* sm2 = new Semaphore(30);   																											
Semaphore* sm3 = new Semaphore(10);   																																																																																						
const int fn = 75;
const int All_v = 264347;
const int fullspace = 5;
string subgraphBound="sampleBoundData/sampleBoundData_SubBound/subgraphBound";
string sub_bound_skylines="sampleBoundData/sampleBoundData_2DSky/sub_bound_skylines";
//######################################################################################





const int INF = 999999999;  
int tree_width = 0;
const int cost_num = 4;//change the value to control the constraints number
const int consider_n = 4;
vector<map<int, int>> VMap;
vector<pair<int, int>> tmp_rectangle;
vector<int> SpaceEnumeration(int n) {
	vector<int> ll_1;
	vector<int> ll_2;
	ll_2.push_back(0);
	for (int i = 0; i < (1 << n); i++) //0～2^5-1
	{

		int key = 0;
		for (int j = 0; j < n; j++) 
		{
			if (i & (1 << j))
			{
				key = key + (int)round(pow(2, j));
			}
		}
		ll_1.push_back(key);
	}

	for (int i = 0; i < n; i++) {
		int a = 1 << i;
		ll_2.push_back(a);
	}

	vector<int> v_diff1;
	set_difference(ll_1.begin(), ll_1.end(), ll_2.begin(), ll_2.end(), inserter(v_diff1, v_diff1.begin()));
	return v_diff1;
}

unordered_map<int, bool> checkEnumeration(vector<int>& SE) {
	unordered_map<int, bool> CE;
	int s = SE.size();
	for (int i = 0; i < s; i++) {
		CE.insert(make_pair(SE[i], false));
	}
	return CE;
}

unordered_map<int, vector<int>> IPOS() {
	unordered_map<int, vector<int>> IP;
	vector<int> pos;
	vector<int> pos1;
	vector<int> SE;
	SE = SpaceEnumeration(fullspace);
	pos.push_back(0);
	int s = SE.size();
	for (int i = 0; i < s; i++) {
		int cnt = 0;
		for (cnt = 0; SE[i]; ++cnt) {
			SE[i] &= (SE[i] - 1);
		}
		if (cnt == 2) {
			IP.insert(make_pair(SE[i], pos));
		}
		else {
			IP.insert(make_pair(SE[i], pos1));
		}

	}
	return IP;
}

int nChoosek(int n, int k)
{
	if (k > n) return 0;
	if (k * 2 > n) k = n - k;
	if (k == 0) return 1;

	int result = n;
	for (int i = 2; i <= k; ++i) {
		result *= (n - i + 1);
		result /= i;
	}
	return result;
}


struct Graph
{
	int n, m, sum;
	vector< map< int, int > > W, Orign_W;
	vector< map< int, vector<int> > > Costs;
	vector< map< int, vector<int> > > Orign_Cost;
	vector<pair<int, vector<int>>> es;
	vector<pair<int, vector<int>>> Orign_es;
	vector<vector<int>> r_VMap;
	pair<int, vector<int>> s;
	pair<int, vector<int>>  Orign_s;
	vector < map<int, vector<pair<int, vector<int>>>>> skylines, Edge;
	vector < map<int, vector<pair<int, vector<int>>>>> Orign_Edge;
	vector<unordered_map<int, unordered_map<int, vector<int>>>> EdgeInSub;

	vector<vector<int>> bound_ord;

	int* DD, * DD2, * NUM;
	int* _DD, * _DD2;
	bool* changed;
	bool* isBound;

	vector<int> D, Orign_D, B_D, BD;

	Graph() {
		n = m = 0;
		sum = 0;
		W.clear();
		Orign_Edge.clear();
		Costs.clear();
		Edge.clear();
		EdgeInSub.clear();
		bound_ord.clear();


	}
	Graph(char* file, char* subFile, int sub_num, int func) {
		//	cout << "file:" << file << endl;
		vector< map< int, int > > Orign_W;

		vector< map< int, vector<int> > >  Orign_Cost;

		Orign_W.clear();

		Orign_Cost.clear();

		Graph();
		ifstream ifs(file);

		if (!ifs.is_open()) {
			cout << "open file error!" << endl;
		}
		ifs >> sum >> m;
		n = sum;
		map<int, int> tmp;
		VMap.resize(n + 1);

		for (int i = 0; i <= sum; i++) {
			map< int, int > v;
			map< int, vector<int> > tmp1;

			int tmp2;
			v.clear();
			tmp1.clear();
			tmp1[i].push_back(tmp2);
			Orign_W.push_back(v);
			Orign_Cost.push_back(tmp1);
		}

		Orign_Edge.resize(sum + 1);
		int x, y, w, c = 0;
		vector<int> nCost;
		for (int i = 0; i < m; i++) {

			ifs >> x >> y >> w;
			nCost.clear();
			for (int k = 0; k < cost_num; k++) {
				ifs >> c;
				nCost.push_back(c);
			}
			if (x > sum || y > sum)
				continue;
			if (Orign_W[x].find(y) != Orign_W[x].end() || Orign_Cost[x].find(y) != Orign_Cost[x].end()) {
				if (Orign_W[x][y] > w) {
					Orign_W[x][y] = w;
					Orign_W[y][x] = w;
					Orign_Cost[x][y] = nCost;
					Orign_Cost[y][x] = nCost;
				}
			}
			else {
				Orign_W[x].insert(make_pair(y, w));
				Orign_W[y].insert(make_pair(x, w));
				Orign_Cost[x].insert(make_pair(y, nCost));
				Orign_Cost[y].insert(make_pair(x, nCost));
				s = make_pair(w, nCost);
				es.push_back(s);

				Orign_Edge[x].insert(make_pair(y, es));
				Orign_Edge[y].insert(make_pair(x, es));

				es.clear();
			}
		}
		Orign_D.clear();
		Orign_D.push_back(0);
		for (int i = 1; i <= sum; i++)
			Orign_D.push_back(Orign_Edge[i].size());

		bound_ord.resize(fn);

		if (func == 0) {
			Sub_Graph(subFile, sub_num, Orign_W, Orign_Cost);
		}
		if (func == 1) {
			cout << "Start to build bound tree..." << endl;
			Bound_Graph(subFile, sub_num, Orign_W, Orign_Cost);
		}
	}

	void Sub_Graph(char* file, int subN, vector< map< int, int > > Orign_W, vector< map< int, vector<int> > > Orign_Cost) {

		ifstream ifs_s(file);
		if (!ifs_s.is_open()) {
			cout << "open file error!" << endl;
		}
		int tem;
		int _tem = 0;
		ifs_s >> n;
		r_VMap.resize(fn);
		for (int i = 0; i < n + 1; i++) {
			r_VMap[subN].push_back(_tem);
		}
		for (int i = 0; i < n; i++) {
			ifs_s >> tem;
			VMap[tem].insert(make_pair(subN, i + 1));
			r_VMap[subN][i + 1] = tem;
		}
		ifs_s.close();

		for (int i = 0; i <= n; i++) {
			map< int, int > v;
			map< int, vector<int> > tmp1;

			int tmp2;
			v.clear();
			tmp1.clear();
			tmp1[i].push_back(tmp2);
			W.push_back(v);
			Costs.push_back(tmp1);
		}

		unordered_map<int, vector<int>> tmp_posInSub;
		tmp_posInSub = IPOS();

		bool check;
		Edge.clear();
		Edge.resize(n + 1);
		EdgeInSub.resize(n + 1);
		
		int x, y, w = 0;
		vector<int> nCosts;
		for (int i = 0; i < n; ++i) {
			for (int j = 0; j < n; ++j) {
				check = isEdgeExist_Orign(r_VMap[subN][i + 1], r_VMap[subN][j + 1]);
				if (check) {
					x = i + 1;
					y = j + 1;
					w = Orign_W[r_VMap[subN][i + 1]][r_VMap[subN][j + 1]];
					nCosts = Orign_Cost[r_VMap[subN][i + 1]][r_VMap[subN][j + 1]];
					if (x > n || y > n)
						continue;
					if (W[x].find(y) != W[x].end() || Costs[x].find(y) != Costs[x].end()) {
						if (W[x][y] > w) {
							W[x][y] = w;
							W[y][x] = w;
							Costs[x][y] = nCosts;
							Costs[y][x] = nCosts;
							s = make_pair(w, nCosts);
							es.push_back(s);

							Edge[x][y] = es;
							Edge[y][x] = es;


							es.clear();

							EdgeInSub[x][y] = tmp_posInSub;
							EdgeInSub[y][x] = tmp_posInSub;
						}
					}
					else {
						W[x].insert(make_pair(y, w));
						W[y].insert(make_pair(x, w));
						Costs[x].insert(make_pair(y, nCosts));
						Costs[y].insert(make_pair(x, nCosts));
						s = make_pair(w, nCosts);
						es.push_back(s);

						Edge[x].insert(make_pair(y, es));
						Edge[y].insert(make_pair(x, es));


						es.clear();

						EdgeInSub[x].insert(make_pair(y, tmp_posInSub));
						EdgeInSub[y].insert(make_pair(x, tmp_posInSub));
					}
				}
			}
		}

		string aa = "";
		string bb = "";


		bb = to_string(static_cast<long long>(subN));
		for (int i1 = 1; i1 < fullspace; i1++) {
			for (int i2 = i1 + 1; i2 < fullspace + 1; i2++) {
				int dd = i1 * 10 + i2;
				int dd_2 = (1 << (fullspace - i1)) + (1 << (fullspace - i2));
				aa = to_string(static_cast<long long>(dd));
				ifstream in(sub_bound_skylines + bb + "dim" + aa + ".txt");
				char str[255];
				int cnt = 0;
				while (!in.eof()) {
					in.getline(str, sizeof(str));
					cnt++;
				}
				in.close();
				ifstream in_s(sub_bound_skylines + bb + "dim" + aa + ".txt");
				cout << "cnt:" << cnt << endl;
				vector<int> nCosts;
				for (int i = 0; i < cnt - 1; i++) {
					nCosts.clear();
					int x, y, w, c = 0;
					in_s >> x >> y >> w;
					for (int j = 0; j < cost_num; j++) {
						in_s >> c;
						nCosts.push_back(c);
					}
					x = VMap[x][subN];
					y = VMap[y][subN];
					s = make_pair(w, nCosts);

					if (Edge[x].find(y) != Edge[x].end() || Edge[y].find(x) != Edge[y].end()) {
						bool dul = false;
						int k = 0;
						for (; k < Edge[x][y].size(); k++) {
							int count = 0;
							if (Edge[x][y][k].first == w) {
								for (int ic = 0; ic < cost_num; ic++) {
									if (Edge[x][y][k].second[ic] != nCosts[ic]) {
										break;
									}
									count++;
								}
							}
							if (count == cost_num) {
								dul = true;
								break;
							}
						}
						if (!dul) {
							Edge[x][y].push_back(s);
							Edge[y][x].push_back(s);
							int si = Edge[x][y].size();
							EdgeInSub[x][y][dd_2].push_back(si - 1);
							EdgeInSub[y][x][dd_2].push_back(si - 1);
						}
						else {

							EdgeInSub[x][y][dd_2].push_back(k);
							EdgeInSub[y][x][dd_2].push_back(k);

						}
					}
					else {
						es.clear();
						es.push_back(s);
						Edge[x].insert(make_pair(y, es));
						Edge[y].insert(make_pair(x, es));
						es.clear();
						//wait to check
						EdgeInSub[x].insert(make_pair(y, tmp_posInSub));
						EdgeInSub[y].insert(make_pair(x, tmp_posInSub));
					}
				}
				in_s.close();
			}

		}




		D.clear();
		D.push_back(0);
		for (int i = 1; i <= n; i++)
			D.push_back(Edge[i].size());

	}
	void Bound_Graph(char* file, int subN, vector< map< int, int > > Orign_W, vector< map< int, vector<int> > > Orign_Cost) {
		cout << "file:" << file << endl;
		ifstream ifs(file);
		int tem;
		int _tem = 0;
		VMap.clear();
		
		if (!ifs.is_open()) {
			cout << "open file error!" << endl;
		}
		ifs >> n;
		VMap.resize(All_v + 1);
		r_VMap.resize(fn + 1);
		for (int i = 0; i < n + 1; i++) {
			r_VMap[subN].push_back(_tem);
		}
		for (int i = 0; i < n; i++) {
			ifs >> tem;
			VMap[tem].insert(make_pair(subN, i + 1));
			r_VMap[subN][i + 1] = tem;
		}
		ifs.close();
		for (int i = 0; i <= n; i++) {
			map< int, int > v;
			map<int, vector<int>> tmp1;
			int tmp2;
			v.clear();
			tmp1.clear();
			tmp1[i].push_back(tmp2);
			W.push_back(v);
			Costs.push_back(tmp1);
		}
		bool check;
		Edge.clear();
		EdgeInSub.clear();
		Edge.resize(n + 1);
		EdgeInSub.resize(n + 1);
		unordered_map<int, vector<int>> tmp_posInSub;
		tmp_posInSub = IPOS();
		string aa = "";
		string bb = "";
		for (int i = 0; i < fn; i++) {
			bb = to_string(static_cast<long long>(i));
			for (int i1 = 1; i1 < fullspace; i1++) {
				for (int i2 = i1 + 1; i2 < fullspace + 1; i2++) {
					int dd = 10 * i1 + i2;
					int dd_2 = (1 << (fullspace - i1)) + (1 << (fullspace - i2));
					aa = to_string(static_cast<long long>(dd));

					ifstream in(sub_bound_skylines + bb + "dim" + aa + ".txt");
					char str[255];
					int cnt = 0;
					while (!in.eof()) {
						in.getline(str, sizeof(str));
						cnt++;
					}
					in.close();

					ifstream in_s(sub_bound_skylines + bb + "dim" + aa + ".txt");
		
					vector<int>  nCosts;
					nCosts.resize(cost_num);
					int x, y, w, c = 0;
					bool iwarn = false;
					for (int j = 0; j < cnt; j++) {
						in_s >> x >> y >> w;
						nCosts.clear();
						if (w == INF) {
							iwarn = true;
						}
						for (int k = 0; k < cost_num; k++) {
							in_s >> c;
							nCosts.push_back(c);
						}
						x = VMap[x][subN];
						y = VMap[y][subN];
						s = make_pair(w, nCosts);

						if (Edge[x].find(y) != Edge[x].end() || Edge[y].find(x) != Edge[y].end()) {
							bool dul = false;
							int k = 0;
							for (; k < Edge[x][y].size(); k++) {
								int count = 0;
								if (Edge[x][y][k].first == w) {
									for (int ic = 0; ic < cost_num; ic++) {
										if (Edge[x][y][k].second[ic] != nCosts[ic]) {
											break;
										}
										count++;
									}
								}
								if (count == cost_num) {
									dul = true;
									break;
								}
							}
							if (!dul) {						
								Edge[x][y].push_back(s);
								Edge[y][x].push_back(s);
								cout << "x:\t" << y << "\ty:\t" << x << "\t" << Edge[y][x][0].first << endl;
								int si = Edge[x][y].size();
								EdgeInSub[x][y][dd_2].push_back(si - 1);
								EdgeInSub[y][x][dd_2].push_back(si - 1);
							}
							else {

								EdgeInSub[x][y][dd_2].push_back(k);
								EdgeInSub[y][x][dd_2].push_back(k);

							}
						}
						else {
							es.clear();
							es.push_back(s);
							//cout << "x:\t" << x << "\ty:\t" << y << "\t" << s.first << endl;
							Edge[x].insert(make_pair(y, es));
							Edge[y].insert(make_pair(x, es));
							es.clear();
							cout << "x:\t" << y << "\ty:\t" << x << "\t" << Edge[y][x][0].first << endl;
							//wait to check
							EdgeInSub[x].insert(make_pair(y, tmp_posInSub));
							EdgeInSub[y].insert(make_pair(x, tmp_posInSub));
						}
					}
					in_s.close();
					if (iwarn) {
						cout << "bb\t" << bb << "\taa\t"<<aa<< endl;
					}
				}
			}
		}

		ifstream in_s("cutEdge_sampleData.txt");
		if (!in_s.is_open()) {
			cout << "open file error!" << endl;
		}
		int cnt;
		in_s >> cnt;
		for (int i = 0; i < cnt; i++) {
			int x, y, w;
			vector<int> nCosts;
			in_s >> x >> y;
			w = Orign_W[x][y];
			nCosts = Orign_Cost[x][y];
			x = VMap[x][subN];
			y = VMap[y][subN];

			bool check = false;
			check = isEdgeExist(x, y);
			if (!check) {
				s = make_pair(w, nCosts);
				es.push_back(s);
				Edge[x].insert(make_pair(y, es));
				Edge[y].insert(make_pair(x, es));

				es.clear();
				EdgeInSub[x][y] = tmp_posInSub;
				EdgeInSub[y][x] = tmp_posInSub;
			}
		}
		in_s.close();
		cout << "cut edge readed!" << endl;
		D.clear();
		D.push_back(0);
		for (int i = 1; i <= n; i++) {
			D.push_back(Edge[i].size());
		}
		

	}

	bool isEdgeExist_Orign(int u, int v) {
		if (Orign_Edge[u].find(v) == Orign_Edge[u].end())
			return false;
		else return true;
	}

	bool isEdgeExist(int u, int v) {
		if (Edge[u].find(v) == Edge[u].end() && EdgeInSub[u].find(v) == EdgeInSub[u].end())
			return false;
		else return true;
	}



	void insertEdge(int u, int v, vector<pair<int, vector<int>>> e, unordered_map<int, vector<int>>p) {
		if (Edge[u].find(v) != Edge[u].end() && EdgeInSub[u].find(v) != EdgeInSub[u].end()) return;
		Edge[u].insert(make_pair(v, e));
		Edge[v].insert(make_pair(u, e));
		EdgeInSub[u].insert(make_pair(v, p));
		EdgeInSub[v].insert(make_pair(u, p));
		D[u]++;
		D[v]++;
	}

	void deleteEdge(int u, int v) {
		if (Edge[u].find(v) == Edge[u].end()) return;
		//cout << Edge[u].size() << " " << Edge[v].size() << endl;
		Edge[u].erase(Edge[u].find(v));
		Edge[v].erase(Edge[v].find(u));
		EdgeInSub[u].erase(EdgeInSub[u].find(v));
		EdgeInSub[v].erase(EdgeInSub[v].find(u));
		D[u]--;
		D[v]--;
	}
};

struct SelEle {
	int x;
	Graph* G;
	SelEle();
	SelEle(int _x, Graph* _g) {
		x = _x;
		G = _g;
	}
	bool operator< (const SelEle se)const {
		if (G->DD[x] != G->DD[se.x])
			return G->DD[x] < G->DD[se.x];
		if (G->DD2[x] != G->DD2[se.x])
			return G->DD2[x] < G->DD2[se.x];
		return x < se.x;
	}
};

struct Node {
	vector<int> vert, pos;
	vector<int> ch;
	vector<vector<pair<int, vector<int>>>> skyToAnc, SK;
	vector<unordered_map<int, vector<int>>> TPIS_ANS, TPIS;
	int height;
	int pa;
	int uniqueVertex;
	Node() {
		vert.clear();
		pos.clear();
		skyToAnc.clear();
		TPIS_ANS.clear();
		ch.clear();
		TPIS.clear();
		pa = -1;
		uniqueVertex = -1;
		height = 0;
	}
};

struct Sub_Tree_Decomposition {
	Graph G, H;
	set<SelEle> deg;
	int maxSize;
	Sub_Tree_Decomposition() {}
	vector<vector<int>> neighbor;
	vector<vector<vector<pair<int, vector<int>>>>> adj_skyline;
	vector<vector<unordered_map<int, vector<int>>>> adj_posInSub;
	vector<int> ord;
	int heightMax;

	struct judge {
		bool operator()(const pair<int, vector<int>> a, const pair<int, vector<int>> b) {
			return a.first < b.first;
		};
	};

	struct hop {
		int i;
		int j;
		pair<int, vector<int>> val;
		hop(int x, int y, pair<int, vector<int>> v) : i(x), j(y), val(v) {};
	};


	struct vectJudge {
		bool operator()(const pair<int, int> a, const pair<int, int> b) {
			return a.second < b.second;
		}
	};

	struct vectJudge2 {
		bool operator()(int a, int b) {
			return a < b;
		}
	};

	void mergeSort(const vector<pair<int, vector<int>>>& s1, const vector<pair<int, vector<int>>>& s2, vector<pair<int, vector<int>>>& result) {
		int size1 = s1.size();
		int size2 = s2.size();
		result.resize(size1 + size2);
		int tmp_index, tmp_1_index, tmp_2_index;
		tmp_1_index = 0;
		tmp_2_index = 0;
		for (tmp_index = 0; (tmp_1_index < size1) && (tmp_2_index < size2); tmp_index++) {
			if (s1[tmp_1_index].first <= s2[tmp_2_index].first) {

				result[tmp_index] = s1[tmp_1_index];
				tmp_1_index++;
			}
			else {
				result[tmp_index] = s2[tmp_2_index];
				tmp_2_index++;
			}
		}
		if (tmp_1_index == size1) {
			while (tmp_2_index < size2) {
				result[tmp_index] = s2[tmp_2_index];
				tmp_index++;
				tmp_2_index++;
			}
		}
		else if (tmp_2_index == size2) {
			while (tmp_1_index < size1) {
				result[tmp_index] = s1[tmp_1_index];
				tmp_index++;
				tmp_1_index++;
			}
		}
	}



	vector < map<int, vector<pair<int, vector<int>>>>> Orign_Edge;
	vector<unordered_map<int, unordered_map<int, vector<int>>>> EdgeInSub;

	inline vector<pair<int, vector<int>>> concatenation2(vector<pair<int, vector<int>>>& h1, vector<pair<int, vector<int>>>& h2) {
		vector<pair<int, vector<int>>> result;

		vector<vector<int>> candi;
		judge ju;

		int s1 = h1.size();
		int s2 = h2.size();
		//change var
		vector<int> C, R;
		R.resize(fullspace);
		for (int k = 0; k < consider_n; k++) {

			C.push_back(INF);
		}
		/*if (s1 == 0 || s2 == 0) {
			result.push_back(make_pair(INF, C));
			return result;
		}*/
		pair<int, vector<int>>BP;
		double etp_min = INF;

		BP = make_pair(INF, C);
		for (int i = 0; i < s1; i++) {
			for (int j = 0; j < s2; j++) {
				int w, c;
				double lnw, lnc, etp;
				bool check = false;
				int cnt = 0;
				w = h1[i].first + h2[j].first;
				R[0] = w;
				etp = log(w);
				if (w >= BP.first) cnt++;
				for (int k = 0; k < consider_n; k++) {
					c = h1[i].second[k] + h2[j].second[k];
					lnc = log(c);
					etp = etp + lnc;
					if (c >= BP.second[k]) {
						cnt++;
					}
					C[k] = c;
					R[k + 1] = c;
				}
				if (cnt == fullspace) {
					check = true;
				}
				if (!check) {
					candi.push_back(R);
					if (etp < etp_min) {
						etp_min = etp;
						BP = make_pair(w, C);
					}

				}
			}
		}

		candi = refine(candi);
		sort(candi.begin(), candi.end());
		candi.erase(unique(candi.begin(), candi.end()), candi.end());
		for (int i = 0; i < candi.size(); i++) {
			for (int j = 0; j < consider_n; j++) {
				C[j] = candi[i][j];
			}
			result.push_back(make_pair(candi[i][0], C));
		}
		//cout << "result size"<<result.size() << endl;
		return result;


	}

	inline vector<pair<int, vector<int>>> concatenation(vector<pair<int, vector<int>>>& h1, vector<pair<int, vector<int>>>& h2) {
		vector<pair<int, vector<int>>> result;


		judge ju;

		int s1 = h1.size();
		int s2 = h2.size();
		//change var
		set<pair<double, int>> sort_Etp;
		vector<int> C;
		for (int k = 0; k < consider_n; k++) {

			C.push_back(INF);
		}
		if (s1 == 0 || s2 == 0) {
			result.push_back(make_pair(INF, C));
			return result;
		}

		for (int i = 0; i < s1; i++) {
			for (int j = 0; j < s2; j++) {
				int w, c;
				double lnw, lnc, etp;
				bool check = false;
				if (sort_Etp.size() >= 10) {
					//vector<pair<int, vector<int>>> BP;
					int count = 0;
					for (set<pair<double,int>>::iterator it=sort_Etp.begin(); it!=sort_Etp.end(); it++) {
						int cnt = 0;
						int tmp=it->second;
						pair<int, vector<int>> BP = result[tmp];
						w = h1[i].first + h2[j].first;
						etp = log(w);
						if (w >= BP.first) cnt++;
						for (int k = 0; k < consider_n; k++) {
							c = h1[i].second[k] + h2[j].second[k];
							lnc = log(c);
							etp = etp + lnc;
							if (c >= BP.second[k]) {
								cnt++;
							}
							C[k] = c;
						}
						if (cnt == fullspace) {
							check = true;
							break;
						}
							
						count++;
						if (count == 10) {
							break;
						}
					}
					if (!check) {
						result.push_back(make_pair(w, C));
						sort_Etp.insert(make_pair(etp, result.size() - 1));
					}
				}
				else
				{
					w = h1[i].first + h2[j].first;
					etp = log(w);
					for (int k = 0; k < consider_n; k++) {
						c = h1[i].second[k] + h2[j].second[k];
						lnc = log(c);
						etp = etp + lnc;
						C[k] = c;
					}
					result.push_back(make_pair(w, C));
					sort_Etp.insert(make_pair(etp, result.size() - 1));
				}
			
			}
		}

		//cout << "result size"<<result.size() << endl;
		return result;


	}
	inline vector<pair<int, vector<int>>> entropy(vector<pair<int, vector<int>>>& input,int num) {
		vector<pair<int, vector<int>>> result;
		vector<vector<pair<int, int>>> rankVector;
		vectJudge vJu;
		
		int size = input.size();
		if (size < 100) {
			pair<int, vector<int>> tmp;
			tmp = input[(int)(size / 2)];
			result.push_back(tmp);
			return result;
		}

		rankVector.resize(fullspace);
		for (int i = 0; i < size; i++) {
			rankVector[0].push_back(make_pair(i, input[i].first));
		}
		for (int ct = 0; ct < fullspace-1; ct++) {
			for (int i = 0; i < size; i++) {
				rankVector[ct+1].push_back(make_pair(i, input[i].second[ct]));
			}
			sort(rankVector[ct+1].begin(), rankVector[ct+1].end(), vJu);
		}

		vector<int> normbase;
		for (int ct = 0; ct < fullspace; ct++) {
			int range = rankVector[ct][0].second - rankVector[ct][size - 1].second+1;
			normbase.push_back(range);
		}
		vector<pair<int, double>> etp_v;
		for (int i = 0; i < size; i++) {
			double etp;
			double norm = (input[i].first - rankVector[0][0].second) / normbase[0] + 1;
			double d0 = log(norm);
			etp = d0;
			for (int ct = 0; ct < fullspace-1; ct++) {
				norm = (input[i].second[ct] - rankVector[ct][0].second) / normbase[ct + 1] + 1;
				double dc = log(norm);
				etp = etp + dc;
			}
			etp_v.push_back(make_pair(i, etp));
		}
		sort(etp_v.begin(), etp_v.end(), vJu);
		for (int i = 0; i < num; i++) {
			int id = etp_v[i].first;
			result.push_back(input[id]);
		}

		return result;

	}
	inline vector<pair<int, vector<int>>> concatenation_withCheck(vector<pair<int, vector<int>>>& h1, vector<pair<int, vector<int>>>& h2, vector<pair<int, vector<int>>>& Block) {
		vector<pair<int, vector<int>>> result;


		judge ju;

		int s1 = h1.size();
		int s2 = h2.size();
		//change var

		vector<int> C;
		set<pair<double, int>> sort_Etp;
		for (int k = 0; k < consider_n; k++) {

			C.push_back(INF);
		}
		if (s1 == 0 || s2 == 0) {
			result.push_back(make_pair(INF, C));
			return result;
		}

		for (int i = 0; i < s1; i++) {
			for (int j = 0; j < s2; j++) {
				int w, c;
				double lnw, lnc, etp;
				bool check = false;
				vector<pair<int, vector<int>>> BP = Block;
				if (result.size() > 10) {
					int count = 0;
					for(set<pair<double, int>>::iterator it = sort_Etp.begin(); it != sort_Etp.end(); it++) {
						count++;
						int tmp = it->second;
						BP.push_back(result[tmp]);
						if (count == 5) break;
					}					
				}
				for (int a = 0; a < BP.size(); a++) {
					int cnt = 0;
					w = h1[i].first + h2[j].first;
					etp = log(w);
					if (w >= BP[a].first) cnt++;
					for (int k = 0; k < consider_n; k++) {
						c = h1[i].second[k] + h2[j].second[k];
						lnc = log(c);
						etp = etp + lnc;
						if (c >= BP[a].second[k]) {
							cnt++;
						}
						C[k] = c;
					}
					if (cnt == fullspace)
						check = true;
						break;
				}
						
				if (!check) {
					result.push_back(make_pair(w, C));
					sort_Etp.insert(make_pair(etp, result.size() - 1));
				}
			}
		}

		//cout << "result size"<<result.size() << endl;
		return result;


	}

	void reduce(int subN) {
		deg.clear();
		neighbor.clear();
		adj_skyline.clear();
		adj_posInSub.clear();
		vector<int> vectmp;
		vectmp.clear();
		for (int i = 0; i <= G.n; i++) {
			neighbor.push_back(vectmp);

		}
		adj_skyline.resize(G.n + 1);
		adj_posInSub.resize(G.n + 1);
		//_s.push_back(make_pair(INF, INF));

		//vector<vector<unordered_map<int, vector<int>>>>


		bool* _exist;
		_exist = (bool*)malloc(sizeof(bool) * (G.n + 1));
		for (int i = 1; i <= G.n; i++)
			_exist[i] = true;


		G.DD = (int*)malloc(sizeof(int) * (G.n + 1));
		G.DD2 = (int*)malloc(sizeof(int) * (G.n + 1));
		G._DD = (int*)malloc(sizeof(int) * (G.n + 1));
		G._DD2 = (int*)malloc(sizeof(int) * (G.n + 1));
		G.NUM = (int*)malloc(sizeof(int) * (G.n + 1));
		G.changed = (bool*)malloc(sizeof(bool) * (G.n + 1));
		G.isBound = (bool*)malloc(sizeof(bool) * (G.n + 1));
		for (int i = 0; i <= G.n; i++)
			G.NUM[i] = i;
		for (int i = 1; i <= G.n; i++) {
			int j = rand() % G.n + 1;
			int x = G.NUM[i];
			G.NUM[i] = G.NUM[j];
			G.NUM[j] = x;
		}
		for (int i = 1; i <= G.n; i++) {
			G.DD[i] = G.D[i];
			G.DD2[i] = G.D[i];
			G._DD[i] = G.D[i];
			G._DD2[i] = G.D[i];
			G.changed[i] = false;
			G.isBound[i] = false;
			deg.insert(SelEle(i, &G));
		}

		int b_size;
		vector<int> sub_b;
		vector<int> b_ord;
		string bb = "";
		bb = to_string(static_cast<long long>(subN));

		ifstream read_bound(subgraphBound + bb + ".txt");

		read_bound >> b_size;
		sub_b.resize(b_size);

		for (int i = 0; i < b_size; i++) {
			int bds;
			read_bound >> bds;
			int map_bds = VMap[bds][subN];
			sub_b[i] = map_bds;
			G.isBound[map_bds] = true;
		}



		bool* exist;
		exist = (bool*)malloc(sizeof(bool) * (G.n + 1));
		for (int i = 1; i <= G.n; i++)
			exist[i] = true;
		ord.clear();

		int cnt = 0;

		while (!deg.empty())
		{
			vector<int> neigh;
			vector<int> neigh_bound;
			vector<vector<pair<int, vector<int>>>> adjsk;
			vector<unordered_map<int, vector<int>>> adjpos;

			judge ju;

			cnt++;
			//cout << cnt << endl;
			int x = (*deg.begin()).x;
			while (true) {
				if (G.changed[x]) {
					deg.erase(SelEle(x, &G));
					G.DD[x] = G._DD[x];
					G.DD2[x] = G._DD2[x];
					deg.insert(SelEle(x, &G));
					G.changed[x] = false;
					x = (*deg.begin()).x;
				}
				else break;
			}
			if (!G.isBound[x]) {
				ord.push_back(x);
			}

			deg.erase(deg.begin());
			
			if (G.isBound[x]) {
				b_ord.push_back(x);
				continue;
			}
			exist[x] = false;

			neigh.clear();
			adjsk.clear();
			adjpos.clear();
			neigh_bound.clear();

			for (map<int, vector<pair<int, vector<int>>>>::iterator it = G.Edge[x].begin(); it != G.Edge[x].end(); it++) {
				int y = (*it).first;
				if (exist[y]) {
					neigh.push_back(y);
					adjsk.push_back((*it).second);
					adjpos.push_back(G.EdgeInSub[x][y]);

				}
			}

			int k = -1;
			for (int i = 0; i < neigh.size(); i++) {
				int y = neigh[i];
				G.deleteEdge(x, y);
				G._DD[y] = G.D[y];
				G.changed[y] = true;
			}


			vector<pair<int, vector<int>>> uv_sk_tmp;
			vector<int> tmp_c;
			unordered_map<int, vector<int>> tmpPos;

			tmpPos = IPOS();

			for (int i = 0; i < consider_n; i++) {
				tmp_c.push_back(INF);
			}
			uv_sk_tmp.push_back(make_pair(INF, tmp_c));
			for (int pu = 0; pu < neigh.size() - 1; pu++) {
				for (int pv = pu + 1; pv < neigh.size(); pv++) {
					if (pu != pv) {
						int u = neigh[pu];
						int v = neigh[pv];


						if (G.isEdgeExist(u, v)) {
							continue;
						}
						else {
							G.insertEdge(u, v, uv_sk_tmp, tmpPos);
							G._DD[u] = G.D[u];
							G._DD[v] = G.D[v];
							++G._DD2[u];
							++G._DD2[v];
							G.changed[u] = true;
							G.changed[v] = true;
						}
					}
				}
			}


			vector<pair<int, vector<int>>> u_sk;
			vector<vector<int>> neighSlides;
			vector<vector<vector<pair<int, vector<int>>>>> adjskSlides;
			vector<int> vT;
			neighSlides.assign(ism1, vT);
			adjskSlides.resize(ism1);
			
			for (int it = 0; it < neigh.size(); it++) {
				neighSlides[it % ism1].push_back(neigh[it]);
				adjskSlides[it % ism1].push_back(adjsk[it]);
			}
		

			for (int pu = 0; pu < neigh.size(); pu++) {
				int u = neigh[pu];
				//cout<<"this u: "<<u<<endl;
				//cout <<"x"<<x<<"\t"<< "u: " <<u<<endl;
				u_sk = adjsk[pu];

				if (G.isBound[u]) {
					//cout << "compute on bound" << endl;
					boost::thread_group threads;
					for (int _it = 0; _it < ism1; _it++)
					{
						if (!neighSlides[_it].empty())
						{
							
							threads.add_thread(new boost::thread(&Sub_Tree_Decomposition::computeNeigh_bound, this, u, boost::ref(neighSlides[_it]), boost::ref(adjskSlides[_it]), boost::ref(u_sk)));
							
						}
					}
					threads.join_all();
				}
				else {
					//cout << "compute without bound" << endl;
					boost::thread_group threads;
					for (int _it = 0; _it < ism1; _it++)
					{
						
						if (!neighSlides[_it].empty())
						{
							
							threads.add_thread(new boost::thread(&Sub_Tree_Decomposition::computeNeigh, this, u, boost::ref(neighSlides[_it]), boost::ref(adjskSlides[_it]), boost::ref(u_sk)));
							
						}
					}
					threads.join_all();

				}



			}
			if (neigh.size() > tree_width)
				tree_width = neigh.size();
			neighbor[x] = neigh;
			adj_skyline[x] = adjsk;
			adj_posInSub[x] = adjpos;
		}

		if (deg.empty()) {
			for (auto& x : b_ord)
			{
				vector<int> neigh;
				vector<vector<pair<int, vector<int>>>> adjsk;
				vector<unordered_map<int, vector<int>>> adjpos;
				judge ju;
				cnt++;
				int bound;
				int b_len = b_ord.size();

				ord.push_back(x);
				exist[x] = false;

				neigh.clear();
				adjsk.clear();
				adjpos.clear();

				for (map<int, vector<pair<int, vector<int>>>>::iterator it = G.Edge[x].begin(); it != G.Edge[x].end(); it++) {
					int y = (*it).first;


					if (exist[y]) {
						neigh.push_back(y);
						adjsk.push_back((*it).second);
						adjpos.push_back(G.EdgeInSub[x][y]);
					}
				}

				int k = -1;
				for (int i = 0; i < neigh.size(); i++) {
					int y = neigh[i];
					G.deleteEdge(x, y);

				}
				vector<pair<int, vector<int>>> uv_sk_tmp;
				vector<int> tmp_c;
				unordered_map<int, vector<int>> tmpPos;

				tmpPos = IPOS();
				for (int i = 0; i < consider_n; i++) {
					tmp_c.push_back(INF);
				}
				uv_sk_tmp.push_back(make_pair(INF, tmp_c));
				for (int pu = 0; pu < neigh.size(); pu++) {
					for (int pv = pu + 1; pv < neigh.size(); pv++) {
						if (pu != pv) {
							int u = neigh[pu];
							int v = neigh[pv];


							if (G.isEdgeExist(u, v)) {
								continue;
							}
							else {
								G.insertEdge(u, v, uv_sk_tmp, tmpPos);
							}
						}
					}
				}


				vector<pair<int, vector<int>>> u_sk;
				unordered_map<int, vector<int>> u_pis;
				vector<vector<int>> neighSlides;
				vector<vector<vector<pair<int, vector<int>>>>> adjskSlides;
				vector<int> vT;
				vector<vector<unordered_map<int, vector<int>>>> pisSlides;
				neighSlides.assign(ism1, vT);
				adjskSlides.resize(ism1);
				pisSlides.resize(ism1);
				for (int it = 0; it < neigh.size(); it++) {
					neighSlides[it % ism1].push_back(neigh[it]);
					adjskSlides[it % ism1].push_back(adjsk[it]);
					pisSlides[it % ism1].push_back(adjpos[it]);
				}

				for (int pu = 0; pu < neigh.size(); pu++) {
					int u = neigh[pu];
					u_sk = adjsk[pu];
					u_pis = adjpos[pu];
					if (G.isBound[u]) {
						boost::thread_group threads;
						for (int _it = 0; _it < ism1; _it++)
						{
							if (!neighSlides[_it].empty())
							{

								threads.add_thread(new boost::thread(&Sub_Tree_Decomposition::computeNeigh_bound, this, u, boost::ref(neighSlides[_it]), boost::ref(adjskSlides[_it]), boost::ref(u_sk)));
							
							}
						}
						threads.join_all();
					}
					else {
						boost::thread_group threads;
						for (int _it = 0; _it < ism1; _it++)
						{
							if (!neighSlides[_it].empty())
							{

								threads.add_thread(new boost::thread(&Sub_Tree_Decomposition::computeNeigh, this, u, boost::ref(neighSlides[_it]), boost::ref(adjskSlides[_it]), boost::ref(u_sk)));
								
							}
						}
						threads.join_all();

					}

				}
				if (neigh.size() > tree_width)
					tree_width = neigh.size();
				neighbor[x] = neigh;
				adj_skyline[x] = adjsk;
				adj_posInSub[x] = adjpos;
			}
		}

		for (int i = 0; i < b_ord.size(); i++) {
			G.bound_ord[subN].push_back(G.r_VMap[subN][b_ord[i]]);
		}

		free(G.DD);
		free(G.DD2);
		free(exist);
	}

	unordered_map<int, vector<int>> DominationOperator(vector<pair<int, vector<int>>>& input) {
		//input is sorted by weight
		unordered_map<int, vector<int>> result;
		vector<vector<pair<int, int>>> rankVector;
		vectJudge vJu;
		vector<int> SE;
		
		//create a check list;
		vector<pair<int, int>> ll;

		int size = input.size();
		result.clear();
		rankVector.resize(consider_n);
		SE = SpaceEnumeration(fullspace);

		if (size <= 1) {
			result = IPOS();
			return result;
		}

		//sort every cost in rankVector
		for (int ct = 0; ct < consider_n; ct++) {
			for (int i = 0; i < size; i++) {
				rankVector[ct].push_back(make_pair(i, input[i].second[ct]));
			}
			sort(rankVector[ct].begin(), rankVector[ct].end(), vJu);
		}


		for (int i = 0; i < size; i++) {
			unordered_map<int, bool> CE;
			CE = checkEnumeration(SE);
			ll.assign(size, make_pair(0, 0));

			//scan the paths that have greater path values than p_i
			bool isSky = true;
			for (int j = 0; j < i; j++) {
				int temp_v = (int)round(pow(2, consider_n - 0));
				ll[j] = make_pair(1, temp_v);
			}
			for (int ct = 0; ct < consider_n; ct++) {
				for (vector<pair<int, int>>::iterator it = rankVector[ct].begin(); it != rankVector[ct].end(); it++) {
					if ((*it).second <= input[i].second[ct] && (*it).first != i) {
						ll[(*it).first].first = ll[(*it).first].first + 1;
						ll[(*it).first].second = ll[(*it).first].second + (int)round(pow(2, consider_n - (ct + 1)));
						if (ll[(*it).first].first == fullspace) {
							isSky = false;
							break;
						}
					}
					else {
						break;
					}
				}
				if (!isSky) {
					break;
				}
			}
			if (!isSky) {
				continue;
			}

            int full=(int)round(pow(2, fullspace))-1;
			if (isSky) {
				CE[full] = true;
			}


			//eliminate all the dominated space 
			vector<int> domSpace;
			for (int vl = 0; vl < size; vl++) {
				if (ll[vl].first >= 2) {
					domSpace.push_back(ll[vl].second);
				}
			}

			sort(domSpace.begin(), domSpace.end());
			domSpace.erase(unique(domSpace.begin(), domSpace.end()), domSpace.end());
			int dom_size = domSpace.size();
			//for each upper level space, eliminate all its subspaces
			for (int vi = 0; vi < dom_size; vi++) {
				CE[domSpace[vi]] = true;
				if (domSpace[vi] > 2) {
					for (int k = 0; k < (1 << fullspace); k++) {
						if (((k & domSpace[vi]) == k) && k != domSpace[vi]) {
							CE[k] = true;
						}
					}
				}
			}

			//eliminate all the superspaces of any skyline subspace
			for (int vi = 1; vi < fullspace; vi++) {
				int d2x = 1 << vi;
				for (int vj = 0; vj < vi; vj++) {
					int d2y = 1 << vj;
					int d2xy = d2x + d2y;
					if (CE[d2xy] == false) {
						//cout << "d2xy: " <<d2xy<<endl;
						for (int k = 0; k < (1 << fullspace); k++) {
							if (((k & d2xy) == d2xy) && k != d2xy) {
								//cout << "k: " <<k<<endl;
								CE[k] = true;
							}
						}
					}
				}
			}

			//record the number of current eliminated subspaces on each level>2
			vector<int> level_check;
			level_check.assign(fullspace + 1, 0);
			for (unordered_map<int, bool>::iterator it = CE.begin(); it != CE.end(); it++) {
				int key = (*it).first;
				if ((*it).second) {
					int cnt = 0;
					for (cnt = 0; key; ++cnt) {
						key &= (key - 1);
					}
					level_check[cnt]++;
				}
			}

			//check level 3
			//
			int vi = 3;
			bool ck = false;
			int domD = nChoosek(fullspace, vi);
			if (level_check[vi] != domD) {
				for (int v1 = 2; v1 < fullspace; v1++) {
					int d3x = 1 << v1;
					for (int v2 = 1; v2 < v1; v2++) {
						int d3y = 1 << v2;
						for (int v3 = 0; v3 < v2; v3++) {
							int d3z = 1 << v3;
							int d3xyz = d3x + d3y + d3z;
							if (CE[d3xyz] == false) {
								for (int k = 0; k < fullspace; k++) {
									if ((d3xyz >> k) & 1) {
										continue;
									}
									else {
										int d4 = d3xyz | (1 << (k));
										CE[d4] = true;
										level_check[4]++;
										if (level_check[4] == 5) {
											ck = true;
											break;
										}
									}
								}
							}
							if (ck) break;
						}
						if (ck) break;
					}
					if (ck) break;
				}
			}

			//assign i to IPOS
			for (unordered_map<int, bool>::iterator it = CE.begin(); it != CE.end(); it++) {
				int key = (*it).first;
				int kk = (*it).second;
				if (!kk) {
					result[key].push_back(i);
				}
			}
		}

		return result;
	}

	vector<pair<int, vector<int>>> DominationOperator_onFull(vector<pair<int, vector<int>>>& input) {
		//input is sorted by weight
		vector<pair<int, vector<int>>> result;
		vector<vector<pair<int, int>>> rankVector;
		vectJudge vJu;
		//create a check list;
		vector<pair<int, int>> ll;

		int size = input.size();
		result.clear();
		rankVector.resize(consider_n+1);
		result.push_back(input[0]);
		if (size <= 1) {
			return result;
		}

		//sort every cost in rankVector
		for (int ct = 0; ct < consider_n; ct++) {
			for (int i = 0; i < size; i++) {
				rankVector[ct+1].push_back(make_pair(i, input[i].second[ct]));
			}
			sort(rankVector[ct+1].begin(), rankVector[ct+1].end(), vJu);
		}

		for (int i = 0; i < size; i++) {
			rankVector[0].push_back(make_pair(i, input[i].first));
		}

		for (int i = 1; i < size; i++) {
			if (input[i].first == INF) {
				break;
			}
			int dc = 0;
			int dc_rank = i;
			for (int ct = 1; ct < consider_n + 1; ct++) {
				int my_rank = 0;
				for (vector<pair<int, int>>::iterator it = rankVector[ct].begin(); it != rankVector[ct].end(); it++) {
					if ((*it).second < input[i].second[ct] && (*it).first != i)
						my_rank++;
					else break;
				}
				if (my_rank < dc_rank) {
					dc_rank = my_rank;
					dc = ct;
				}
			}
			int counter = 0;
			int num_map = rankVector[dc].size();
			vector<int> checkList;
			for (int it = 0; it < rankVector[dc].size(); it++) {
				counter++;
				int key = rankVector[dc][it].first;
				if (key == i) {
					break;
				}
				if (key < i) {
					checkList.push_back(key);
				}
			}
			if (counter > num_map* (1 - 1 / consider_n)) {
				continue;
			}
			int dc_check = 0;
			int non_domi = 0;
			if (checkList.size() == 0) {
				result.push_back(input[i]);
				//cout << "check" << endl;
			}
			else {
				for (int it = 0; it < checkList.size(); it++) {
					int key = checkList[it];

					dc_check++;
					for (int r = 0; r < consider_n; r++) {
						if (input[i].second[r] < input[key].second[r]) {
							non_domi++;
							break;
						}
					}

				}
				if (dc_check == non_domi && dc_check != 0) {
					result.push_back(input[i]);
				}
			}
			
		}
		return result;
	}

	inline vector<int> posFilter(unordered_map<int, vector<int>>& posInSub) {
		vector<int> tmp;
		vector<int> ls;
		vector<pair<int, vector<int>>> uv_f;
		unordered_map<int, vector<int>> pos;
		unordered_map<int, vector<int>>::iterator iter;
		iter = posInSub.begin();
		set<int> us;

		while (iter != posInSub.end()) {
			tmp = iter->second;
			for (int i = 0; i < tmp.size(); i++) {
				us.insert(tmp[i]);
			}
			iter++;
		}
		for (auto& it : us)
			ls.push_back(it);
		return ls;
	}

	inline vector<pair<int, vector<int>>> pathFilter(vector<pair<int, vector<int>>>& uv_sk, vector<int>& ls) {
		vector<pair<int, vector<int>>> uv;
		for (int i = 0; i < ls.size(); i++) {
			//cout << "ls[i]: " << ls[i] << endl;
			uv.push_back(uv_sk[ls[i]]);
		}
		return uv;
	}

	inline unordered_map<int, vector<int>> updatePIS(unordered_map<int, vector<int>>& posInSub, vector<int>& ls) {
		unordered_map<int, vector<int>> pis;
		vector<int> tmp;
		map<int, int> dc;

		for (int i = 0; i < ls.size(); i++) {
			int x = ls[i];

			dc.insert(make_pair(x, i));
		}
		auto iter = posInSub.begin();
		while (iter != posInSub.end()) {
			tmp = iter->second;
			int key = iter->first;
			vector<int> pos;
			for (int i = 0; i < tmp.size(); i++) {
				if (dc[tmp[i]] >= ls.size()) {
					cout << "error1" << endl;
				}
				pos.push_back(dc[tmp[i]]);
			}

			pis.insert(make_pair(key, pos));
			++iter;
		}

		//cout << "done" << endl;
		return pis;
	}

	//CONSTRUCTING...
	inline void computeNeigh_bound(int u, vector<int>& neighSlides, vector<vector<pair<int, vector<int>>>>& adjskSlides, vector<pair<int, vector<int>>>& u_sk) {
		sm->wait();
		judge ju;
		int v;
		vector<pair<int, vector<int>>> uv_sk;
		vector<pair<int, vector<int>>> temp;
		//vector<pair<int, vector<int>>> temp1;
		vector<pair<int, vector<int>>> v_sk;

		unordered_map<int, vector<int>> posInSub;
		unordered_map<int, vector<int>> posInSub_s;
		vector<pair<int, vector<int>>> uv_sk_f;//after pathFiter



		for (int pv = 0; pv < neighSlides.size(); pv++) {
			v = neighSlides[pv];
			v_sk = adjskSlides[pv];
			if (G.isBound[v]) {
				//cout << "find bound!" << endl;
				continue;
			}


			if (u > v) {

				vector<int> ls;
				vector<pair<int, int>> bd;
				if (G.Edge[u][v].size() == 1 && G.Edge[u][v][0].first == INF) {

					uv_sk = concatenation(u_sk, v_sk);
					sort(uv_sk.begin(), uv_sk.end(), ju);
					posInSub = DominationOperator(uv_sk);
					ls = posFilter(posInSub);
					uv_sk_f = pathFilter(uv_sk, ls);
					posInSub_s = updatePIS(posInSub, ls);
					G.Edge[u][v] = uv_sk_f;
					G.Edge[v][u] = uv_sk_f;
					G.EdgeInSub[u][v] = posInSub_s;
					G.EdgeInSub[v][u] = posInSub_s;

				}
				else {
					vector<pair<int, vector<int>>> Block = entropy(G.Edge[u][v], 1);
					uv_sk = concatenation_withCheck(u_sk, v_sk,Block);

					sort(uv_sk.begin(), uv_sk.end(), ju);
					mergeSort(G.Edge[u][v], uv_sk, temp);
					posInSub = DominationOperator(temp);
					ls = posFilter(posInSub);
					uv_sk_f = pathFilter(temp, ls);
					posInSub_s = updatePIS(posInSub, ls);
					G.Edge[u][v] = uv_sk_f;
					G.Edge[v][u] = uv_sk_f;
					G.EdgeInSub[u][v] = posInSub_s;
					G.EdgeInSub[v][u] = posInSub_s;
				}
			}
		}
		sm->notify();
	}

#if 1
	inline void computeNeigh(int u, vector<int>& neighSlides, vector<vector<pair<int, vector<int>>>>& adjskSlides, vector<pair<int, vector<int>>>& u_sk) {
		sm->wait();
		judge ju;
		int v;
		vector<pair<int, vector<int>>> uv_sk;
		vector<pair<int, vector<int>>> temp;
		vector<pair<int, vector<int>>> v_sk;

		unordered_map<int, vector<int>> posInSub;
		unordered_map<int, vector<int>> posInSub_s;
		vector<pair<int, vector<int>>> uv_sk_f;//after pathFiter


		for (int pv = 0; pv < neighSlides.size(); pv++) {
			v = neighSlides[pv];
			v_sk = adjskSlides[pv];

			if (u > v) {

				vector<int> ls;
				if (G.Edge[u][v].size() == 1 && G.Edge[u][v][0].first == INF) {
					uv_sk = concatenation(u_sk, v_sk);
					sort(uv_sk.begin(), uv_sk.end(), ju);
					posInSub = DominationOperator(uv_sk);
					ls = posFilter(posInSub);
					uv_sk_f = pathFilter(uv_sk, ls);
					posInSub_s = updatePIS(posInSub, ls);
					G.Edge[u][v] = uv_sk_f;
					G.Edge[v][u] = uv_sk_f;
					G.EdgeInSub[u][v] = posInSub_s;
					G.EdgeInSub[v][u] = posInSub_s;

				}
				else {
					vector<pair<int, vector<int>>> Block = entropy(G.Edge[u][v], 1);
					uv_sk = concatenation_withCheck(u_sk, v_sk, Block);
					sort(uv_sk.begin(), uv_sk.end(), ju);
					mergeSort(G.Edge[u][v], uv_sk, temp);	
					posInSub = DominationOperator(temp);
					ls = posFilter(posInSub);
					uv_sk_f = pathFilter(temp, ls);
					posInSub_s = updatePIS(posInSub, ls);
					G.Edge[u][v] = uv_sk_f;
					G.Edge[v][u] = uv_sk_f;
					G.EdgeInSub[u][v] = posInSub_s;
					G.EdgeInSub[v][u] = posInSub_s;
				}
			}
		}
		sm->notify();
	}
#endif
	vector<Node> Tree;
	int root;
	int* belong, * rank;
	int match(int x, vector<int>& neigh) {
		int nearest = neigh[0];
		for (int i = 1; i < neigh.size(); i++)
		{
			if (rank[neigh[i]] > rank[nearest])
				nearest = neigh[i];
		}
		int p = belong[nearest];
		vector<int> a = Tree[p].vert;
		if (Tree[p].uniqueVertex >= 0) {
			a.push_back(Tree[p].uniqueVertex);
		}
		sort(a.begin(), a.end());
		int i, j;
		for (i = 0, j = 0; (i < neigh.size()) && (j < a.size()); ) {
			if (neigh[i] == a[j]) {
				i++; j++;
			}
			else if (neigh[i] < a[j])
				break;
			else j++;
		}
		if (i >= neigh.size()) {
			return p;
		}
		printf("no match!\n");
	}

	void makeTree() {
		belong = (int*)malloc(sizeof(int) * (H.n + 1));
		rank = (int*)malloc(sizeof(int) * (H.n + 1));
		int len = ord.size() - 1;
		Node rootn;
		Tree.clear();
		heightMax = 0;
		int x = ord[len];
		rootn.vert = neighbor[x];
		rootn.TPIS = adj_posInSub[x];
		rootn.SK = adj_skyline[x];
		rootn.uniqueVertex = x;
		rootn.pa = -1;
		rootn.height = 1;
		rank[x] = 0;
		belong[x] = 0;
		Tree.push_back(rootn);
		len--;

		for (; len >= 0; len--) {
			int x = ord[len];
			int c = 0;
			Node nod;
			nod.vert = neighbor[x];
			nod.SK = adj_skyline[x];
			nod.TPIS = adj_posInSub[x];
			nod.uniqueVertex = x;
			int pa = match(x, neighbor[x]);
			Tree[pa].ch.push_back(Tree.size());
			nod.pa = pa;
			nod.height = Tree[pa].height + 1;
			if (nod.height > heightMax)
				heightMax = nod.height;
			rank[x] = Tree.size();
			belong[x] = Tree.size();
			Tree.push_back(nod);
		}

		root = 0;
	}

	int* toRMQ;
	vector<int> EulerSeq;
	vector<vector<int>> RMQIndex;
	void makeRMQDFS(int p, int height) {
		toRMQ[p] = EulerSeq.size();
		EulerSeq.push_back(p);
		for (int i = 0; i < Tree[p].ch.size(); i++) {
			makeRMQDFS(Tree[p].ch[i], height + 1);
			EulerSeq.push_back(p);
		}
	}
	void makeRMQ() {
		EulerSeq.clear();
		toRMQ = (int*)malloc(sizeof(int) * (G.n + 1));
		makeRMQDFS(root, 1);
		RMQIndex.clear();
		RMQIndex.push_back(EulerSeq);
		int m = EulerSeq.size();
		for (int i = 2, k = 1; i < m; i = i * 2, k++) {
			vector<int> tmp;
			tmp.clear();
			tmp.resize(EulerSeq.size());
			for (int j = 0; j < m - i; j++) {
				int x = RMQIndex[k - 1][j], y = RMQIndex[k - 1][j + i / 2];
				if (Tree[x].height < Tree[y].height)
					tmp[j] = x;
				else tmp[j] = y;
			}
			RMQIndex.push_back(tmp);
		}
	}
	int LCAQuery(int _p, int _q) {
		int p = toRMQ[_p], q = toRMQ[_q];
		if (p > q) {
			int x = p;
			p = q;
			q = x;
		}
		int len = q - p + 1;
		int i = 1, k = 0;
		while (i * 2 < len) {
			i *= 2;
			k++;
		}
		q = q - i + 1;
		if (Tree[RMQIndex[k][p]].height < Tree[RMQIndex[k][q]].height)
			return RMQIndex[k][p];
		else return RMQIndex[k][q];
	}

	vector<pair<int, vector<int>>> distanceQueryAncestorToPosterity(int p, int q) {
		vector<pair<int, vector<int>>> temp;
		vector<int> tmp_C;
		for (int i = 0; i < consider_n; i++) {
			tmp_C.push_back(0);
		}
		temp.push_back(make_pair(0, tmp_C));
		if (p == q) return temp;
		int x = belong[p], y = belong[q];
		return Tree[y].skyToAnc[Tree[x].pos[Tree[x].pos.size() - 1]];
	}

	unordered_map<int, vector<int>> posQueryAncestorToPosterity(int p, int q) {
		unordered_map<int, vector<int>> tmp;
		tmp = IPOS();
		if (p == q) return tmp;
		int x = belong[p], y = belong[q];
		return Tree[y].TPIS_ANS[Tree[x].pos[Tree[x].pos.size() - 1]];
	}

	void calculateIndexSizeDFS(int p, int pre, int tmp, long long& result) {
		for (int i = 0; i < Tree[p].ch.size(); i++) {
			calculateIndexSizeDFS(Tree[p].ch[i], pre + 1, (pre + 1) + tmp, result);
		}
		if (tmp + (pre + 1) > result) result = tmp + (pre + 1);
	}
	long long calculateIndexSize() {
		long long res = Tree[root].vert.size();
		for (int i = 0; i < Tree[root].ch.size(); i++) {
			calculateIndexSizeDFS(Tree[root].ch[i], Tree[root].vert.size(), Tree[root].vert.size(), res);
		}
		return res;
	}

	void makeIndexDFS_new(int p, vector<int>& list, int* toList) {
		judge ju;

		vector<int> C;

		for (int k = 0; k < consider_n; k++) {

			C.push_back(INF);
		}

		Tree[p].pos.resize(Tree[p].vert.size() + 1);
		Tree[p].skyToAnc.resize(list.size());
		Tree[p].TPIS_ANS.resize(list.size());
		for (int i = 0; i < list.size(); i++) {
			Tree[p].skyToAnc[i].resize(list.size());
		}
		//	printf("step1");
		for (int i = 0; i < Tree[p].vert.size(); i++) {
			int j;
			for (j = 0; j < list.size(); j++)
				if (list[j] == Tree[p].vert[i])
					break;
			Tree[p].pos[i] = j;
		}
		Tree[p].pos[Tree[p].vert.size()] = list.size();
		//printf("Step 2");
		pair<int, vector<int>> pp = make_pair(INF, C);
		vector<pair<int, vector<int>>> vp(1, pp);
		Tree[p].skyToAnc.assign(list.size(), vp);

		int x = Tree[p].uniqueVertex;
		if (G.isBound[x]) {
			cout << "Tree<Bound Node> " << p << "\t width:" << Tree[p].pos.size() << endl;
			for (int i = 0; i < list.size(); i++)
			{
				for (int j = 0; j < Tree[p].vert.size(); j++)
				{
					int x = Tree[p].vert[j];
					int y = list[i];
					vector<pair<int, vector<int>>> assign;
					vector<pair<int, vector<int>>> assign_s;
					unordered_map<int, vector<int>> assign_pos;
					vector<int> tmp_ls;
					if (x == y)
					{
						assign = Tree[p].SK[j];
						
						assign_pos = DominationOperator(assign);
						tmp_ls = posFilter(assign_pos);
						assign_s = pathFilter(assign, tmp_ls);
						assign_pos = updatePIS(assign_pos, tmp_ls);
						Tree[p].skyToAnc[toList[x]] = assign_s;
						Tree[p].TPIS_ANS[toList[x]] = assign_pos;
						continue;
					}
				}
			}

		}
		else {
			vector<vector<int> > vvInput;
			vector<int> vT;
			vvInput.assign(ism2, vT);
			for (int i = 0; i < list.size(); i++) {
				vvInput[i % ism2].push_back(list[i]);
			}
			vector<vector<pair<int, vector<int>> > > vvpSkyline;
			for (int i = 0; i < Tree[p].vert.size(); i++)
			{
				int x = Tree[p].vert[i];
				vvpSkyline.push_back(Tree[p].SK[i]);
			}
			boost::thread_group threads;
			for (int i = 0; i < ism2; i++)
			{
				if (!vvInput[i].empty())
				{
					threads.add_thread(new boost::thread(&Sub_Tree_Decomposition::propagation, this, p, boost::ref(vvInput[i]), boost::ref(toList), list.size(), boost::ref(list), boost::ref(vvpSkyline)));
				}
			}
			threads.join_all();
		}

		//printf("Step 4");
		toList[Tree[p].uniqueVertex] = list.size();
		list.push_back(Tree[p].uniqueVertex);
		for (int i = 0; i < Tree[p].ch.size(); i++) {

			makeIndexDFS_new(Tree[p].ch[i], list, toList);
		}
		list.pop_back();

		sort(Tree[p].pos.begin(), Tree[p].pos.end());
	}


	inline vector<int> cube(vector<vector<pair<int, vector<int>>>>& x, vector<vector<pair<int, vector<int>>>>& y, vector<int>& p) {
		int bbxMin, bbyMin, bbxMax, bbyMax;
		vector<int> res;
		vector<vector<pair<int, vector<int>>>> hops;
		vector<pair<int, vector<int>>> upperleft;
		vector<pair<int, vector<int>>> downright;

		judge ju;
		vectJudge2 vJu;
		hops.resize(p.size());
		if (p.size() == 1) {
			res.push_back(0);
			return res;
		}


		vector<vector<int>> lowbound_x;
		vector<vector<int>> highbound_x;
		vector<vector<int>> lowbound_y;
		vector<vector<int>> highbound_y;

		lowbound_x.resize(p.size());
		lowbound_y.resize(p.size());
		highbound_x.resize(p.size());
		highbound_y.resize(p.size());

		vector<vector<int>> lowbound;
		vector<vector<int>> highbound;
		lowbound.resize(p.size());
		highbound.resize(p.size());

		vector<vector<int>> d_min_x;
		vector<vector<int>> d_min_y;
		vector<vector<int>> d_max_x;
		vector<vector<int>> d_max_y;
		d_min_x.resize(consider_n);
		d_min_y.resize(consider_n);
		d_max_x.resize(consider_n);
		d_max_y.resize(consider_n);
		//cout << "check1" << endl;
		for (int i = 0; i < p.size(); ++i) {
			d_min_x.clear();
			d_min_y.clear();
			d_max_x.clear();
			d_max_y.clear();

			for (int z = 0; z < consider_n; z++) {
				vector<int> tmp_sortV;
				for (int j = 0; j < x[p[i]].size(); ++j) {
					tmp_sortV.push_back(x[p[i]][j].second[z]);
				}
				sort(tmp_sortV.begin(), tmp_sortV.end(), vJu);
				d_min_x[z].push_back(tmp_sortV[0]);
				d_max_x[z].push_back(tmp_sortV[tmp_sortV.size() - 1]);
			}
			for (int it = 0; it < consider_n; it++) {
				lowbound_x[i].push_back(d_min_x[it][0]);
				highbound_x[i].push_back(d_max_x[it][0]);
			}

			for (int z = 0; z < consider_n; z++) {
				vector<int> tmp_sortV;
				for (int j = 0; j < y[p[i]].size(); ++j) {
					tmp_sortV.push_back(y[p[i]][j].second[z]);
				}
				sort(tmp_sortV.begin(), tmp_sortV.end(), vJu);
				d_min_y[z].push_back(tmp_sortV[0]);
				d_max_y[z].push_back(tmp_sortV[tmp_sortV.size() - 1]);
			}
			for (int it = 0; it < consider_n; it++) {
				lowbound_y[i].push_back(d_min_y[it][0]);
				highbound_y[i].push_back(d_max_y[it][0]);
			}
		}
		for (int i = 0; i < p.size(); ++i) {
			lowbound[i].push_back(x[p[i]][0].first + y[p[i]][0].first);
			highbound[i].push_back(x[p[i]][x[p[i]].size() - 1].first + y[p[i]][y[p[i]].size() - 1].first);

			for (int j = 0; j < consider_n; ++j) {
				int tmp_low = lowbound_x[i][j] + lowbound_y[i][j];
				int tmp_high = highbound_x[i][j] + highbound_y[i][j];
				lowbound[i].push_back(tmp_low);
				highbound[i].push_back(tmp_high);
			}
		}
		vector<int> deleteList;
		for (int i = 0; i < p.size() - 1; ++i) {
			int counter = 0;
			int _counter = 0;

			int size_d = deleteList.size();
			if (size_d > 0) {
				bool check = false;
				for (int j = 0; j < size_d; j++) {
					if (i == deleteList[j]) {
						check = true;
					}
				}
				if (check) {
					continue;
				}
			}
			for (int j = i + 1; j < p.size(); ++j) {
				for (int k = 0; k < consider_n + 1; k++) {
					if (highbound[i][k] <= lowbound[j][k]) {
						counter++;
					}
					if (lowbound[i][k] >= highbound[j][k]) {
						_counter++;
					}
				}
				if (counter == consider_n + 1) {
					deleteList.push_back(j);
				}
				if (_counter == consider_n + 1) {
					deleteList.push_back(i);
					break;
				}
			}
		}
		//cout << "check4" << endl;
		for (int i = 0; i < p.size(); i++) {
			vector<int>::iterator it;
			it = std::find(deleteList.begin(), deleteList.end(), i);
			if (it == deleteList.end()) {
				res.push_back(i);
			}
		}
		return res;
	}

	inline vector<pair<int, vector<int>>> concatenation_og(vector<pair<int, vector<int>>>& h1, vector<pair<int, vector<int>>>& h2) {
		vector<pair<int, vector<int>>> result;
		judge ju;

		int s1 = h1.size();
		int s2 = h2.size();
		vector<int> C;
		for (int k = 0; k < consider_n; k++) {

			C.push_back(INF);
		}

		for (int i = 0; i < s1; i++) {
			for (int j = 0; j < s2; j++) {
				int w, c;
				int cnt = 0;
				w = h1[i].first + h2[j].first;
				for (int k = 0; k < consider_n; k++) {
					c = h1[i].second[k] + h2[j].second[k];
					C[k] = c;
				}
				result.push_back(make_pair(w, C));
			}
		}
		return result;
	}

	void propagation(int p, vector<int>& list, int* toList, int ancNum, vector<int>& ancList, vector<vector<pair<int, vector<int>>>>& vvpSkyline) {
		sm2->wait();
		vector<pair<int, vector<int>>> z;
		vector<pair<int, vector<int>>> _z;
		vector<pair<int, vector<int>>> zz_s;
		unordered_map<int, vector<int>> posInSub;
		vector<int> ls;
		vector<vector<int>> hpList;
		vector<vector<vector<pair<int, vector<int>>>>> H1;
		vector<vector<vector<pair<int, vector<int>>>>> H2;
		if (Tree[p].vert.size() < 8) {
			for (int i = 0; i < list.size(); i++)
			{
				int y = list[i];
				//int sizecount = 0;
				for (int j = 0; j < Tree[p].vert.size(); j++)
				{
					int x = Tree[p].vert[j];

					vector<pair<int, vector<int>>> assign;
					vector<pair<int, vector<int>>> assign_s;
					unordered_map<int, vector<int>> assign_pos;
					vector<pair<int, vector<int>>> zz;
					vector<int> tmp_ls;
					if (x == y)
					{
						mergeSort(vvpSkyline[j], Tree[p].SK[j], assign);	
						assign_pos = DominationOperator(assign);
						tmp_ls = posFilter(assign_pos);
						assign_s = pathFilter(assign, tmp_ls);
						assign_pos = updatePIS(assign_pos, tmp_ls);
						

						Tree[p].skyToAnc[toList[x]] = assign_s;
						Tree[p].TPIS_ANS[toList[x]] = assign_pos;
						continue;
					}
					int ix, iy;
					for (int k = 0; k < ancList.size(); k++)
					{
						if (ancList[k] == x)
							ix = k;
						if (ancList[k] == y)
							iy = k;
					}

					if (ix < iy)
					{
						z = distanceQueryAncestorToPosterity(x, y);
					}
					else
					{
						z = distanceQueryAncestorToPosterity(y, x);
					}
					vector<pair<int, vector<int>>> Block = entropy(Tree[p].skyToAnc[toList[y]], 3);
					_z = concatenation_withCheck(z, vvpSkyline[j], Block);
					mergeSort(_z, Tree[p].skyToAnc[toList[y]], zz);
					posInSub = DominationOperator(zz);
					//cout << "d" << endl;
					ls = posFilter(posInSub);
					zz_s = pathFilter(zz, ls);
					posInSub = updatePIS(posInSub, ls);
					Tree[p].skyToAnc[toList[y]] = zz_s;
					Tree[p].TPIS_ANS[toList[y]] = posInSub;
				}
			}
		}
		else {
			for (int i = 0; i < list.size(); i++)
			{
				vector<int> p_set;
				vector<vector<pair<int, vector<int>>>> h1;
				vector<vector<pair<int, vector<int>>>> h2;
				vector<int> hp;
				for (int j = 0; j < Tree[p].vert.size(); j++) {
					int x = Tree[p].vert[j];
					int y = list[i];
					int ix, iy;
					for (int k = 0; k < ancList.size(); k++)
					{
						if (ancList[k] == x)
							ix = k;
						if (ancList[k] == y)
							iy = k;
					}

					if (ix < iy)
					{
						z = distanceQueryAncestorToPosterity(x, y);
					
					}
					else
					{
						z = distanceQueryAncestorToPosterity(y, x);
					}
					h1.push_back(z);
					h2.push_back(vvpSkyline[j]);
					p_set.push_back(j);
				}
				H1.push_back(h1);
				H2.push_back(h2);
				hp = cube(h1, h2, p_set);
				hpList.push_back(hp);
			}

			//	cout << "Merging" << endl;
			for (int i = 0; i < list.size(); i++) {
				for (int j = 0; j < Tree[p].vert.size(); j++)
				{
					int x = Tree[p].vert[j];
					int y = list[i];
					vector<pair<int, vector<int>>> assign;
					vector<pair<int, vector<int>>> assign_s;
					unordered_map<int, vector<int>> assign_pos;
					vector<int> tmp_ls;
					if (x == y)
					{
						mergeSort(vvpSkyline[j], Tree[p].SK[j], assign);	
						assign_pos = DominationOperator(assign);
						tmp_ls = posFilter(assign_pos);
						assign_s = pathFilter(assign, tmp_ls);
						assign_pos = updatePIS(assign_pos, tmp_ls);
					

						Tree[p].skyToAnc[toList[x]] = assign_s;
						Tree[p].TPIS_ANS[toList[x]] = assign_pos;
						continue;
					}
				}
			}

			for (int i = 0; i < list.size(); i++) {
				vector<int> hp;
				vector<pair<int, vector<int>>> zz;
				int y = list[i];
				hp = hpList[i];
				for (int vi = 0; vi < hp.size(); vi++) {
					vector<pair<int, vector<int>>> Block = entropy(Tree[p].skyToAnc[toList[y]], 1);
					zz.clear();
					_z = concatenation_withCheck(H1[i][hp[vi]], H2[i][hp[vi]], Block);				
					mergeSort(_z, Tree[p].skyToAnc[toList[y]], zz);
					posInSub = DominationOperator(zz);
					ls = posFilter(posInSub);
					zz_s = pathFilter(zz, ls);			 
					posInSub = updatePIS(posInSub, ls);
					Tree[p].skyToAnc[toList[y]] = zz_s;
					Tree[p].TPIS_ANS[toList[y]] = posInSub;
					
				}

			}
		}

		sm2->notify();
	}

	vector<pair<int, vector<int>>> upper;
	vector<pair<int, vector<int>>> lower;

	vector<vector<int>> refine(vector<vector<int>>& input) {
		vector<vector<pair<int, int>>> rankVector;
		vector<vector<pair<int, int>>> rankbound;
		vectJudge vJu;;
		vector<vector<int>> bound;
		vector<vector<int>> re;
		int size = input.size();
		rankVector.resize(fullspace);
		rankbound.resize(fullspace);
		if (size <= 10) {
			return input;
		}
		//sort every cost in rankVector
		for (int ct = 0; ct < fullspace; ct++) {
			for (int i = 0; i < size; i++) {
				rankVector[ct].push_back(make_pair(i, input[i][ct]));
			}
			sort(rankVector[ct].begin(), rankVector[ct].end(), vJu);
		}

		for (int i = 0; i < fullspace; i++) {
			int tmp;
			tmp = rankVector[i][0].first;
			bound.push_back(input[tmp]);
		}

		for (int ct = 0; ct < fullspace; ct++) {

			for (int i = 0; i < bound.size(); i++) {
				rankbound[ct].push_back(make_pair(i, bound[i][ct]));
			}
			sort(rankbound[ct].begin(), rankbound[ct].end(), vJu);
		}

		for (int i = 0; i < size; i++) {
			int cnt = 0;
			for (int ct = 0; ct < fullspace; ct++) {
				int min, max;

				min = rankbound[ct][0].second;
				max = rankbound[ct][rankbound[ct].size() - 1].second;
				if (input[i][ct] <= max) {
					cnt++;
				}
			}
			if (cnt == fullspace) {
				re.push_back(input[i]);
			}
		}

		return re;

	}

	
	void makeIndex() {
		makeRMQ();
		//H.EdgeInitialize();
		//printCSPCHIndex();
	}

	void readPositionIndex(string file, vector<vector<int>>& position) {
		ifstream in(file);
		if (!in.is_open()) {
			cout << "open file error!" << endl;
		}
		string line;
		vector<int> temp;
		while (getline(in, line)) {
			stringstream ss(line);
			int x;
			while (ss >> x) {
				//cout << x << '\t';
				temp.push_back(x);
			}
			position.push_back(temp);
			temp.clear();
			//cout << endl;
		}
		in.close();
	}

	void readSkylineIndex(string file) {
		ifstream in(file);
		if (!in.is_open()) {
			cout << "open file error!" << endl;
		}
		int n, ns, vert, sks;
		vector<int> C;
		for (; in >> n >> ns >> vert >> sks;) {
			Tree[n].skyToAnc.resize(ns);
			for (int i = 0; i < sks; i++) {
				int x, y;
				in >> x;
				C.clear();
				for (int k = 0; k < consider_n; k++) {
					in >> y;
					C.push_back(y);
				}
				Tree[n].skyToAnc[vert].push_back(make_pair(x, C));
			}
		}
		in.close();
	}
	void readPosInSubIndex(string file) {
		ifstream in(file);
		if (!in.is_open()) {
			cout << "open file error!" << endl;
		}
		int n, ns, vert, sks;
		vector<int> C;
		for (; in >> n >> ns >> vert;) {
			Tree[n].TPIS_ANS.resize(ns);
			for (int i = 0; i < ns; i++) {
				for (int j = 0; j < 26; j++) {
					int key, tps, po;
					in >> key >> tps;
					vector<int> tmp;
					for (int k = 0; k < tps; k++) {
						in >> po;
						tmp.push_back(po);
					}
					Tree[n].TPIS_ANS[i].insert(make_pair(key, tmp));
				}

			}
		}
		in.close();
	}

#if 0
	void printCSPCHIndex() {
		ofstream outfile;
		outfile.open("order_index(NY_R).txt");
		for (int i = 0; i < ord.size(); i++) {
			outfile << i << '\t' << ord[i] << endl;
		}
		outfile.close();

		ofstream outfile1;
		outfile1.open("CSPCH_index(NY_R).txt");
		for (int i = 0; i < Tree.size(); i++) {
			//outfile1 << i << '\t';
			for (int j = 0; j < Tree[i].SK.size(); j++) {
				outfile1 << Tree[i].uniqueVertex << '\t' << Tree[i].SK.size() << '\t' << Tree[i].vert[j] << '\t' << Tree[i].SK[j].size() << '\t';
				for (int k = 0; k < Tree[i].SK[j].size(); k++) {
					outfile1 << Tree[i].SK[j][k].first << '\t';
					for (int p = 0; p < consider_n; p++) {
						outfile1 << Tree[i].SK[j][k].second[p] << '\t';
					}
				}
				outfile1 << endl;
			}
		}
		outfile1.close();
	}
#endif
	void printIndex(int a) {
		string bb = "";
		bb = to_string(static_cast<long long>(a));
		ofstream outfile;
		outfile.open("FHL_Index/position_index(sub)" + bb + ".txt");
		for (int i = 0; i < Tree.size(); i++) {
			if (Tree[i].pos.size() > 9999) {
				Tree[i].pos.clear();
				continue;
			}
			for (int j = 0; j < Tree[i].pos.size(); j++) {
				outfile << Tree[i].pos[j] << '\t';
			}
			outfile << endl;
		}
		outfile.close();

		ofstream outfile1;
		outfile1.open("FHL_Index/skyline_index(sub)" + bb + ".txt");
		for (int i = 0; i < Tree.size(); i++) {
			//outfile1 << i << '\t';
			for (int j = 0; j < Tree[i].skyToAnc.size(); j++) {
				outfile1 << i << '\t' << Tree[i].skyToAnc.size() << '\t' << j << '\t' << Tree[i].skyToAnc[j].size() << '\t';
				for (int k = 0; k < Tree[i].skyToAnc[j].size(); k++) {
					outfile1 << Tree[i].skyToAnc[j][k].first << '\t';
					for (int p = 0; p < consider_n; p++) {
						outfile1 << Tree[i].skyToAnc[j][k].second[p] << '\t';
					}
				}
				outfile1 << endl;
			}
		}
		outfile1.close();

		ofstream outfile2;
		outfile2.open("FHL_Index/edgeInSub_index(sub)" + bb + ".txt");
		for (int i = 0; i < Tree.size(); i++) {
			//outfile1 << i << '\t';
			for (int j = 0; j < Tree[i].TPIS_ANS.size(); j++) {
				outfile2 << i << '\t' << Tree[i].TPIS_ANS.size() << '\t' << j << '\t';
				for (auto& it : Tree[i].TPIS_ANS[j]) {
					vector<int> tmp = it.second;
					outfile2 << it.first << '\t' << tmp.size() << '\t';
					for (int p = 0; p < tmp.size(); p++) {
						outfile2 << tmp[p] << '\t';
					}
				}
				outfile2 << endl;
			}
		}
		outfile2.close();

		ofstream outfile3;
		outfile3.open("FHL_Index/contract_ord(sub)" + bb + ".txt");
		outfile3 << G.bound_ord[a].size() << endl;
		for (int i = 0; i < G.bound_ord[a].size(); i++) {
			outfile3 << G.bound_ord[a][i] << endl;
		}
		outfile3.close();
	}
	/*
	void printIndex_onFull(int a) {
		string bb = "";
		bb = to_string(static_cast<long long>(a));
		ofstream outfile;
		outfile.open("FHL_Index/position_index(sub)" + bb + ".txt");
		for (int i = 0; i < Tree.size(); i++) {
			if (Tree[i].pos.size() > 9999) {
				Tree[i].pos.clear();
				continue;
			}
			for (int j = 0; j < Tree[i].pos.size(); j++) {
				outfile << Tree[i].pos[j] << '\t';
			}
			outfile << endl;
		}
		outfile.close();

		ofstream outfile1;
		outfile1.open("FHL_Index/skyline_index(sub)" + bb + ".txt");
		for (int i = 0; i < Tree.size(); i++) {
			//outfile1 << i << '\t';
			for (int j = 0; j < Tree[i].skyToAnc.size(); j++) {
				outfile1 << i << '\t' << Tree[i].skyToAnc.size() << '\t' << j << '\t' << Tree[i].skyToAnc[j].size() << '\t';
				for (int k = 0; k < Tree[i].skyToAnc[j].size(); k++) {
					outfile1 << Tree[i].skyToAnc[j][k].first << '\t';
					for (int p = 0; p < consider_n; p++) {
						outfile1 << Tree[i].skyToAnc[j][k].second[p] << '\t';
					}
				}
				outfile1 << endl;
			}
		}
		outfile1.close();

		ofstream outfile3;
		outfile3.open("FHL_Index/contract_ord(sub)" + bb + ".txt");
		outfile3 << G.bound_ord[a].size() << endl;
		for (int i = 0; i < G.bound_ord[a].size(); i++) {
			outfile3 << G.bound_ord[a][i] << endl;
		}
		outfile3.close();
	}
	*/
	void loadIndex(int a, int i) {

		if (a == 0) {
			cout << "Re-building CSP-2Hop index" << endl;
			makeIndex3();
			reducePos();
			printIndex(i);
		}

		else {
			cout << "Loading CSP-2Hop index" << endl;
			string bb = "";
			bb = to_string(static_cast<long long>(i));

			vector<vector<int>> ps;
			string positionFile = "FHL_Index/position_index(sub)" + bb + ".txt";
			string skylineFile = "FHL_Index/skyline_index(sub)" + bb + ".txt";
			string posInSubFile = "FHL_Index/edgeInSub_index(sub)" + bb + ".txt";
			readPositionIndex(positionFile, ps);
			for (int i = 0; i < ps.size(); i++) {
				Tree[i].pos = ps[i];
			}
			readSkylineIndex(skylineFile);
			readPosInSubIndex(posInSubFile);

		}
	}

	void makeIndex3() {
		vector<int> list;
		list.clear();
		int* toList;
		toList = (int*)malloc(sizeof(int) * (G.n + 1));
		Tree[root].pos.clear();

		toList[Tree[root].uniqueVertex] = 0;
		list.push_back(Tree[root].uniqueVertex);
		Tree[root].pos.push_back(0);

		for (int i = 0; i < Tree[root].ch.size(); ++i) {
			makeIndexDFS_new(Tree[root].ch[i], list, toList);
			break;
		}
		free(toList);

	}

	void reducePosDFS(int p) {
		if (Tree[p].ch.size() == 2) {
			int t = Tree[p].ch[0];
			if (Tree[Tree[p].ch[0]].pos.size() > Tree[Tree[p].ch[1]].pos.size())
				t = Tree[p].ch[1];
			Tree[p].pos = Tree[t].pos;
			Tree[p].pos.erase(Tree[p].pos.begin() + (Tree[p].pos.size() - 1));
		}
		for (int i = 0; i < Tree[p].ch.size(); i++)
			reducePosDFS(Tree[p].ch[i]);
	}
	void reducePos() {
		reducePosDFS(root);
	}
	void cntSize() {
		long long s_nonroot = 0;
		long long s_size = 0;

		long long s_dis = 0;
		for (int i = 0; i < Tree.size(); ++i) {
			s_nonroot += Tree[i].height - 1;
			s_size += Tree[i].vert.size();
			s_dis += Tree[i].height;
		}
		long long s_root = (long long)Tree[0].vert.size() * (long long)G.n;
		printf("tree width: %d\n", tree_width);
		printf("nonroot idx size = %0.3lfGB, avg node size=%0.3lf, avg label size=%0.3lf\n",
			s_nonroot * 4.0 / 1000000000.0, s_size * 1.0 / G.n, s_dis * 1.0 / G.n);
	}

};

struct Graph_bd {
	int n, m;
	vector<int> V;
	vector< map< int, int > > E;
	vector<int> D;

	int* DD, * DD2, * NUM;
	int* _DD, * _DD2;
	bool* changed;
	Graph_bd() {
		n = m = 0;
		V.clear();
		E.clear();
	}
	Graph_bd(char* file) {
		//	cout << "file:" << file << endl;
		Graph();
		ifstream ifs(file);
		ifs >> n >> m;
		
		for (int i = 0; i <= n; i++) {
			map< int, int > v;
			v.clear();
			E.push_back(v);
		}
		for (int i = 0; i < m; i++) {
			int x, y;
			int z = INF;
			ifs >> x >> y;
			x = x + 1;
			y = y + 1;
			if (x > n || y > n)
				continue;
			if (E[x].find(y) != E[x].end()) {
				if (E[x][y] > z) {
					E[x][y] = z;
					E[y][x] = z;
				}
			}
			else {
				E[x].insert(make_pair(y, z));
				E[y].insert(make_pair(x, z));
			}
		}
		D.clear();
		D.push_back(0);
		for (int i = 1; i <= n; i++)
			D.push_back(E[i].size());
	}

	bool isEdgeExist(int u, int v) {
		if (E[u].find(v) == E[u].end())
			return false;
		else return true;
	}
	void insertEdge(int u, int v, int k) {
		if (E[u].find(v) != E[u].end()) return;
		E[u].insert(make_pair(v, k));
		E[v].insert(make_pair(u, k));
		D[u]++;
		D[v]++;
	}
	void deleteEdge(int u, int v) {
		if (E[u].find(v) == E[u].end()) return;
		E[u].erase(E[u].find(v));
		E[v].erase(E[v].find(u));
		D[u]--;
		D[v]--;
	}
};

vector<int> bd_ord;

struct Bound_Tree_Decomposition {
	Graph G, H;
	vector<Sub_Tree_Decomposition> TDs;
	set<SelEle> deg;
	int maxSize;
	Bound_Tree_Decomposition() {}
	vector<vector<int>> neighbor;
	vector<vector<vector<pair<int, vector<int>>>>> adj_skyline;
	vector<vector<unordered_map<int, vector<int>>>> adj_posInSub;
	vector<int> ord;
	int heightMax;
	
	struct judge {
		bool operator()(const pair<int, vector<int>> a, const pair<int, vector<int>> b) {
			if (a.first == b.first)
				return a.second[0] < b.second[0];
			return a.first < b.first;
		};
	};

	struct judgeEtp {
		bool operator()(const pair<double, pair<int, vector<int>>> a, const pair<double, pair<int, vector<int>>> b) {
			return a.first< b.first;
		}
	};
	
	struct judge2 {
		bool operator()(const pair<int, int> a, const pair<int, int> b) {
			return a.first <= b.first;
		};
	};


	struct hop {
		int i;
		int j;
		pair<int, vector<int>> val;
		hop(int x, int y, pair<int, vector<int>> v) : i(x), j(y), val(v) {};
	};

	struct pk {
		bool operator()(const hop& a, const hop& b) const {
			return a.val.first < b.val.first;
		}
	};

	struct vectJudge {
		bool operator()(const pair<int, int> a, const pair<int, int> b) {
			return a.second < b.second;
		}
	};

	struct vectJudge_double {
		bool operator()(const pair<int, double> a, const pair<int, double> b) {
			return a.second < b.second;
		}
	};

	struct vectJudge2 {
		bool operator()(int a, int b) {
			return a < b;
		}
	};

	void mergeSort(const vector<pair<int, vector<int>>>& s1, const vector<pair<int, vector<int>>>& s2, vector<pair<int, vector<int>>>& result) {
		int size1 = s1.size();
		int size2 = s2.size();
		result.resize(size1 + size2);
		int tmp_index, tmp_1_index, tmp_2_index;
		tmp_1_index = 0;
		tmp_2_index = 0;
		for (tmp_index = 0; (tmp_1_index < size1) && (tmp_2_index < size2); tmp_index++) {
			if (s1[tmp_1_index].first <= s2[tmp_2_index].first) {

				result[tmp_index] = s1[tmp_1_index];
				tmp_1_index++;
			}
			else {
				result[tmp_index] = s2[tmp_2_index];
				tmp_2_index++;
			}
		}
		if (tmp_1_index == size1) {
			while (tmp_2_index < size2) {
				result[tmp_index] = s2[tmp_2_index];
				tmp_index++;
				tmp_2_index++;
			}
		}
		else if (tmp_2_index == size2) {
			while (tmp_1_index < size1) {
				result[tmp_index] = s1[tmp_1_index];
				tmp_index++;
				tmp_1_index++;
			}
		}
	}

	inline vector<pair<int, vector<int>>> concatenation(vector<pair<int, vector<int>>>& h1, vector<pair<int, vector<int>>>& h2) {
		vector<pair<int, vector<int>>> result;

		vector<vector<int>> candi;
		judge ju;

		int s1 = h1.size();
		int s2 = h2.size();
		//change var
		vector<int> C,R;
		R.resize(fullspace);
		for (int k = 0; k < consider_n; k++) {

			C.push_back(INF);
		}
		/*if (s1 == 0 || s2 == 0) {
			result.push_back(make_pair(INF, C));
			return result;
		}*/
		pair<int, vector<int>>BP;
		double etp_min = INF;

		BP = make_pair(INF,C);
		for (int i = 0; i < s1; i++) {
			for (int j = 0; j < s2; j++) {
				int w, c;
				double lnw, lnc, etp;
				bool check = false;
				int cnt=0;
				w = h1[i].first + h2[j].first;
				R[0] = w;
				etp = log(w);
				if (w >= BP.first) cnt++;
				for (int k = 0; k < consider_n; k++) {
					c = h1[i].second[k] + h2[j].second[k];
					lnc = log(c);
					etp = etp + lnc;
					if (c >= BP.second[k]) {
						cnt++;
					}
					C[k] = c;
					R[k + 1] = c;
				}
				if (cnt == fullspace) {
					check = true;
				}							
				if (!check) {
					candi.push_back(R);
					if (etp < etp_min) {
						etp_min = etp;
						BP = make_pair(w, C);
					}

				}
			}
		}
		
		candi = refine(candi);
		sort(candi.begin(), candi.end());
		candi.erase(unique(candi.begin(), candi.end()), candi.end());
		for (int i = 0; i < candi.size(); i++) {
			for (int j = 0; j < consider_n; j++) {
				C[j] = candi[i][j];
			}
			result.push_back(make_pair(candi[i][0], C));
		}
		return result;


	}
	inline vector<pair<double,pair<int, vector<int>>>> entropy(vector<pair<int, vector<int>>>& input, int num) {
		vector<pair<double, pair<int, vector<int>>>> result;
		vector<vector<pair<int, int>>> rankVector;
		vectJudge_double vJu;
		result.resize(num);
		int size = input.size();
		if (size < 10) {
			vector<pair<double, pair<int, vector<int>>>> result1;
			result1.resize(1);
			pair<int, vector<int>> tmp;
			int s = size / 2;
			tmp = input[s];
			double t2 = 0;
			result1[0] = make_pair(t2, tmp);
			return result1;
		}

		rankVector.resize(fullspace);
		for (int i = 0; i < size; i++) {
			rankVector[0].push_back(make_pair(i, input[i].first));
		}
		for (int ct = 0; ct < fullspace - 1; ct++) {
			for (int i = 0; i < size; i++) {
				rankVector[ct + 1].push_back(make_pair(i, input[i].second[ct]));
			}
			sort(rankVector[ct + 1].begin(), rankVector[ct + 1].end(), vJu);
		}
		vector<pair<int, double>> etp_v;
		for (int i = 0; i < size; i++) {
			double etp;
			//cout << norm << "---" << endl;
			double dw = log(input[i].first);
			//cout << dd << "---==" << endl;
			etp = dw;
			for (int ct = 0; ct < fullspace - 1; ct++) {
				double dc = log(input[i].second[ct]);
				etp = etp + dc;
			}
			etp_v.push_back(make_pair(i, etp));
		}
		sort(etp_v.begin(), etp_v.end(), vJu);
		for (int i = 0; i < num; i++) {
			int id = etp_v[i].first;
			double t1 = etp_v[i].second;
			pair<double, pair<int, vector<int>>> t2;
			t2 = make_pair(t1, input[id]);
			result[i] = t2;
			//result.push_back(t2);
		}

		return result;

	}

	inline vector<pair<int, vector<int>>> concatenation_og(vector<pair<int, vector<int>>>& h1, vector<pair<int, vector<int>>>& h2) {
		vector<pair<int, vector<int>>> result;
		judge ju;

		int s1 = h1.size();
		int s2 = h2.size();
		vector<int> C;
		for (int k = 0; k < consider_n; k++) {

			C.push_back(INF);
		}
		for (int i = 0; i < s1; i++) {
			for (int j = 0; j < s2; j++) {
				int w, c;	
				int cnt = 0;
				w = h1[i].first + h2[j].first;
				for (int k = 0; k < consider_n; k++) {
					c = h1[i].second[k] + h2[j].second[k];
					C[k] = c;
				}
				result.push_back(make_pair(w, C));
			}
		}
		return result;
	}

	inline vector<pair<int, vector<int>>> concatenation_withCheck(vector<pair<int, vector<int>>>& h1, vector<pair<int, vector<int>>>& h2, vector<pair<double, pair<int, vector<int>>>>& Block) {
		vector<pair<int, vector<int>>> result;


		judgeEtp jubp;

		int s1 = h1.size();
		int s2 = h2.size();
		vector<int> C,R;
		vector<vector<int>> candi;
		vector<pair<double, pair<int, vector<int>>>> sort_Etp,BP;
		R.resize(fullspace);
		for (int k = 0; k < consider_n; k++) {

			C.push_back(INF);
		}
		int s = Block.size();
		BP = Block;
		double etp_min;
		//BP = Block[0];
		for (int i = 0; i < s1; i++) {
			for (int j = 0; j < s2; j++) {
				int w,c;
				double lnw, lnc,etp;
				bool check = false;
				w = h1[i].first + h2[j].first;
				etp = log(w);
				R[0] = w;
				for (int k = 0; k < consider_n; k++) {
					c = h1[i].second[k] + h2[j].second[k];
					lnc = log(c);
					etp = etp + lnc;
					C[k] = c;
					R[k + 1] = c;
				}
				for (int a = 0; a < BP.size(); a++) {
					int cnt = 0;

					if (w >= BP[a].second.first) cnt++;
					for (int k = 0; k < consider_n; k++) {
						if (c >= BP[a].second.second[k]) {
							cnt++;
						}
					}
					
					if (cnt == fullspace) {
						check = true;
						break;
					}
				}
											
				if (!check) {
					candi.push_back(R);
				    etp_min = Block[s - 1].first;
					if (etp < etp_min) {
						etp_min = etp;
						pair<int, vector<int>> tmp;
						tmp = make_pair(w, C);
						BP[s-1] = make_pair(etp_min,tmp);
						sort(BP.begin(), BP.end(), jubp);
					}					
				}
			}
		}
		
		candi = refine(candi);
		sort(candi.begin(), candi.end());
		candi.erase(unique(candi.begin(), candi.end()), candi.end());

		for (int i = 0; i < candi.size(); i++) {
			for (int j = 0; j < consider_n; j++) {
				C[j] = candi[i][j];
			}
			result.push_back(make_pair(candi[i][0], C));
		}
		return result;
	}

	vector<vector<int>> refine(vector<vector<int>>& input) {
		vector<vector<pair<int, int>>> rankVector;
		vector<vector<pair<int, int>>> rankbound;
		vectJudge vJu;;
		vector<vector<int>> bound;
		vector<vector<int>> re;
		int size = input.size();
		rankVector.resize(fullspace);
		rankbound.resize(fullspace);
		if (size <= 10) {
			return input;
		}

		//sort every cost in rankVector
		for (int ct = 0; ct < fullspace; ct++) {
			for (int i = 0; i < size; i++) {
				rankVector[ct].push_back(make_pair(i, input[i][ct]));
			}
			sort(rankVector[ct].begin(), rankVector[ct].end(), vJu);
		}

		for (int i = 0; i < fullspace; i++) {
			int tmp;
			tmp = rankVector[i][0].first;
			bound.push_back(input[tmp]);
		}

		for (int ct = 0; ct < fullspace; ct++) {
			
			for (int i = 0; i < bound.size(); i++) {
				rankbound[ct].push_back(make_pair(i, bound[i][ct]));
			}
			sort(rankbound[ct].begin(), rankbound[ct].end(), vJu);
		}
	
		for (int i = 0; i < size; i++) {
			int cnt = 0;
			for (int ct = 0; ct < fullspace; ct++) {
				int min, max;
				
				min = rankbound[ct][0].second;
				max = rankbound[ct][rankbound[ct].size() - 1].second;
				if (input[i][ct] <= max) {
					cnt++;
				}
			}
			if (cnt == fullspace) {
				re.push_back(input[i]);
			}
		}

		return re;

	}
	unordered_map<int, vector<int>> DominationOperator(vector<pair<int, vector<int>>>& input) {
		//input is sorted by weight
		unordered_map<int, vector<int>> result;
		vector<vector<pair<int, int>>> rankVector;
		vector<vector<pair<int, int>>> rankbound;
		vectJudge vJu;
		vector<int> SE;
		vector<pair<int, vector<int>>> bound;
		vector<pair<int, int>> border;
		//create a check list;
		vector<pair<int, int>> ll;

		int size = input.size();
		result.clear();
		rankVector.resize(consider_n);
		SE = SpaceEnumeration(fullspace);

		if (size <= 1) {
			result = IPOS();
			return result;
		}

		//sort every cost in rankVector
		for (int ct = 0; ct < consider_n; ct++) {
			for (int i = 0; i < size; i++) {
				rankVector[ct].push_back(make_pair(i, input[i].second[ct]));
			}
			sort(rankVector[ct].begin(), rankVector[ct].end(), vJu);
		}
	
		
		for (int i = 0; i < size; i++) {
			unordered_map<int, bool> CE;
			CE = checkEnumeration(SE);
			ll.assign(size, make_pair(0, 0));

			//scan the paths that have greater path values than p_i
			bool isSky = true;
			for (int j = 0; j < i; j++) {
				int temp_v = (int)round(pow(2, consider_n - 0));
				ll[j] = make_pair(1, temp_v);
			}
			for (int ct = 0; ct < consider_n; ct++) {
				for (vector<pair<int, int>>::iterator it = rankVector[ct].begin(); it != rankVector[ct].end(); it++) {
					if ((*it).second <= input[i].second[ct] && (*it).first != i) {
						ll[(*it).first].first = ll[(*it).first].first + 1;
						ll[(*it).first].second = ll[(*it).first].second + (int)round(pow(2, consider_n - (ct + 1)));
						if (ll[(*it).first].first == fullspace) {
							isSky = false;
							break;
						}
					}
					else {
						break;
					}
				}
				if (!isSky) {
					break;
				}
			}
			if (!isSky) {
				continue;
			}

            int full=(int)round(pow(2, fullspace))-1;
			if (isSky) {
				CE[full] = true;
			}

			vector<int> domSpace;
			for (int vl = 0; vl < size; vl++) {
				if (ll[vl].first >= 2) {
					domSpace.push_back(ll[vl].second);
				}
			}

			sort(domSpace.begin(), domSpace.end());
			domSpace.erase(unique(domSpace.begin(), domSpace.end()), domSpace.end());
			int dom_size = domSpace.size();
			//for each upper level space, eliminate all its subspaces
			for (int vi = 0; vi < dom_size; vi++) {
				CE[domSpace[vi]] = true;
				if (domSpace[vi] > 2) {
					for (int k = 0; k < (1 << fullspace); k++) {
						if (((k & domSpace[vi]) == k) && k != domSpace[vi]) {
							CE[k] = true;
						}
					}
				}
			}

			//eliminate all the superspaces of any skyline subspace
			for (int vi = 1; vi < fullspace; vi++) {
				int d2x = 1 << vi;
				for (int vj = 0; vj < vi; vj++) {
					int d2y = 1 << vj;
					int d2xy = d2x + d2y;
					if (CE[d2xy] == false) {
						//cout << "d2xy: " <<d2xy<<endl;
						for (int k = 0; k < (1 << fullspace); k++) {
							if (((k & d2xy) == d2xy) && k != d2xy) {
								//cout << "k: " <<k<<endl;
								CE[k] = true;
							}
						}
					}
				}
			}

			//record the number of current eliminated subspaces on each level>2
			vector<int> level_check;
			level_check.assign(fullspace + 1, 0);
			for (unordered_map<int, bool>::iterator it = CE.begin(); it != CE.end(); it++) {
				int key = (*it).first;
				if ((*it).second) {
					int cnt = 0;
					for (cnt = 0; key; ++cnt) {
						key &= (key - 1);
					}
					level_check[cnt]++;
				}
			}

			//check level 3
			//
			int vi = 3;
			bool ck = false;
			int domD = nChoosek(fullspace, vi);
			if (level_check[vi] != domD) {
				for (int v1 = 2; v1 < fullspace; v1++) {
					int d3x = 1 << v1;
					for (int v2 = 1; v2 < v1; v2++) {
						int d3y = 1 << v2;
						for (int v3 = 0; v3 < v2; v3++) {
							int d3z = 1 << v3;
							int d3xyz = d3x + d3y + d3z;
							if (CE[d3xyz] == false) {
								for (int k = 0; k < fullspace; k++) {
									if ((d3xyz >> k) & 1) {
										continue;
									}
									else {
										int d4 = d3xyz | (1 << (k));
										CE[d4] = true;
										level_check[4]++;
										if (level_check[4] == 5) {
											ck = true;
											break;
										}
									}
								}
							}
							if (ck) break;
						}
						if (ck) break;
					}
					if (ck) break;
				}
			}

			for (unordered_map<int, bool>::iterator it = CE.begin(); it != CE.end(); it++) {
				int key = (*it).first;
				int kk = (*it).second;
				if (!kk) {
					result[key].push_back(i);
				}
			}
		}

		return result;
	}
	vector<int> b_map;
	void reduce() {

		neighbor.clear();
		adj_skyline.clear();
		adj_posInSub.clear();
		vector<int> vectmp;
		vectmp.clear();
		for (int i = 0; i <= G.n; i++) {
			neighbor.push_back(vectmp);

		}
		adj_skyline.resize(G.n + 1);
		adj_posInSub.resize(G.n + 1);



		vector<vector<int>> bo;
		vector<pair<int, int>> bo_size;
		vector<int> sub_b;
		//sub_b.reserve(5000);

		bo.resize(fn);
		int count = 0;
		for (int i = 0; i < fn; i++) {
			string bb = "";
			bb = to_string(static_cast<long long>(i));
			ifstream ifs(subgraphBound + bb + ".txt");
			int cnt;
			int bds;
			ifs >> cnt;
			count = count + cnt;
			for (int j = 0; j < cnt; j++) {
				ifs >> bds;
				bo[i].push_back(bds);
			}
			bo_size.push_back(make_pair(bo[i].size(), i));
			ifs.close();

		}

		judge2 ju;
		//vector<int> b_map;
		b_map.resize(count + 1);
		ifstream ifs("bd_ord.txt");
		for (int i = 0; i < fn; i++) {
			int bd;
			ifs >> bd;
			bd_ord.push_back(bd);
		}
		ifs.close();
		
		int count1 = 0;
		
		for (int i = 0; i < fn; i++) {

			int tmp = bd_ord[i];
			for (int j = 0; j < bo[tmp].size(); j++) {
				int map_bds = VMap[bo[tmp][j]][fn];
				if (map_bds != 0) {
					sub_b.push_back(map_bds);
					b_map[map_bds] = tmp;
				}
			}
		}
		cout << "sub size:" << sub_b.size() << endl;
		vector<bool> exist(G.n + 1, true);
		
		ord.clear();
		int cnt = 0;
		while (!sub_b.empty())
		{
			vector<int> neigh;
			vector<vector<pair<int, vector<int>>>> adjsk;
			vector<unordered_map<int, vector<int>>> adjpos;
			judge ju;
			cnt++;
			int bound;
			int x = sub_b[0];

			ord.push_back(x);
			sub_b.erase(sub_b.begin());
			exist[x] = false;

			neigh.clear();
			adjsk.clear();
			adjpos.clear();

			for (map<int, vector<pair<int, vector<int>>>>::iterator it = G.Edge[x].begin(); it != G.Edge[x].end(); it++) {
				int y = (*it).first;
				

				if (exist[y]) {
					
					neigh.push_back(y);
					adjsk.push_back((*it).second);
				
					adjpos.push_back(G.EdgeInSub[x][y]);
					//leng.push_back((*it).second);
				}
			}

			cout << "x: " << x <<"\tnum: "<<cnt<<"\tneigh size:"<<neigh.size()<<endl;
			int k = -1;
			for (int i = 0; i < neigh.size(); i++) {
				int y = neigh[i];
				G.deleteEdge(x, y);

			}
			vector<pair<int, vector<int>>> uv_sk_tmp;
			vector<int> tmp_c;
			unordered_map<int, vector<int>> tmpPos;

			tmpPos = IPOS();
			for (int i = 0; i < consider_n; i++) {
				tmp_c.push_back(INF);
			}
			uv_sk_tmp.push_back(make_pair(INF, tmp_c));
			for (int pu = 0; pu < neigh.size(); pu++) {
				for (int pv = pu + 1; pv < neigh.size(); pv++) {
					if (pu != pv) {
						int u = neigh[pu];
						int v = neigh[pv];


						if (G.isEdgeExist(u, v)) {
							continue;
						}
						else {
							//cout << "here" << endl;
							G.insertEdge(u, v, uv_sk_tmp, tmpPos);
						}
					}
				}
			}


			vector<pair<int, vector<int>>> u_sk;
			unordered_map<int, vector<int>> u_pis;
			vector<vector<int>> neighSlides;
			vector<vector<vector<pair<int, vector<int>>>>> adjskSlides;
			vector<int> vT;
			neighSlides.assign(ism1, vT);
			adjskSlides.resize(ism1);
			for (int it = 0; it < neigh.size(); it++) {
				neighSlides[it % ism1].push_back(neigh[it]);
				adjskSlides[it % ism1].push_back(adjsk[it]);
			}

			for (int pu = 0; pu < neigh.size(); pu++) {
				int u = neigh[pu];
				u_sk = adjsk[pu];
				boost::thread_group threads;
				for (int _it = 0; _it < ism1; _it++)
				{
					if (!neighSlides[_it].empty())
					{
						threads.add_thread(new boost::thread(&Bound_Tree_Decomposition::computeNeigh, this, u, boost::ref(neighSlides[_it]), boost::ref(adjskSlides[_it]), boost::ref(u_sk), boost::ref(b_map)));
						//computeNeigh(u, neighSlides[_it], adjskSlides[_it], u_sk);

					}
				}
				threads.join_all();

			}
			if (neigh.size() > tree_width)
				tree_width = neigh.size();
			neighbor[x] = neigh;
			//cout << "neigh size: " << neigh.size() << endl;
			adj_skyline[x] = adjsk;
			
			adj_posInSub[x] = adjpos;
			//cout << "posInSub size: " << neigh.size() << endl;

		}
	}

	inline vector<int> posFilter(unordered_map<int, vector<int>>& posInSub) {
		vector<int> tmp;
		vector<int> ls;
		vector<pair<int, vector<int>>> uv_f;
		unordered_map<int, vector<int>> pos;
		unordered_map<int, vector<int>>::iterator iter;
		iter = posInSub.begin();

		while (iter != posInSub.end()) {
			tmp = iter->second;
			for (int i = 0; i < tmp.size(); i++) {
				//cout <<"tmp[i]: " << tmp[i] << endl;
				ls.push_back(tmp[i]);
			}
			iter++;
		}
		sort(ls.begin(), ls.end());
		ls.erase(unique(ls.begin(), ls.end()), ls.end());
		return ls;
	}

	inline vector<pair<int, vector<int>>> pathFilter(vector<pair<int, vector<int>>>& uv_sk, vector<int>& ls) {
		vector<pair<int, vector<int>>> uv;
		for (int i = 0; i < ls.size(); i++) {
			uv.push_back(uv_sk[ls[i]]);
		}
		return uv;
	}

	inline unordered_map<int, vector<int>> updatePIS(unordered_map<int, vector<int>>& posInSub, vector<int>& ls) {
		unordered_map<int, vector<int>> pis;
		vector<int> tmp;
		map<int, int> dc;

		for (int i = 0; i < ls.size(); i++) {
			int x = ls[i];

			dc.insert(make_pair(x, i));
		}
		auto iter = posInSub.begin();
		while (iter != posInSub.end()) {
			tmp = iter->second;
			int key = iter->first;
			vector<int> pos;
			for (int i = 0; i < tmp.size(); i++) {
				if (dc[tmp[i]] >= ls.size()) {
					cout << "error1" << endl;
				}
				pos.push_back(dc[tmp[i]]);
			}

			pis.insert(make_pair(key, pos));
			++iter;
		}
		return pis;
	}


	vector<pair<int, vector<int>>> DominationOperator_onFull(vector<pair<int, vector<int>>>& input) {
		//input is sorted by weight
		vector<pair<int, vector<int>>> result;
		vector<vector<pair<int, int>>> rankVector;
		vectJudge vJu;
		//create a check list;
		vector<pair<int, int>> ll;

		int size = input.size();
		result.clear();
		rankVector.resize(consider_n + 1);
		result.push_back(input[0]);
		if (size <= 1) {
			return result;
		}

		//sort every cost in rankVector
		for (int ct = 0; ct < consider_n; ct++) {
			for (int i = 0; i < size; i++) {
				rankVector[ct + 1].push_back(make_pair(i, input[i].second[ct]));
			}
			sort(rankVector[ct + 1].begin(), rankVector[ct + 1].end(), vJu);
		}

		for (int i = 0; i < size; i++) {
			rankVector[0].push_back(make_pair(i, input[i].first));
		}

		for (int i = 1; i < size; i++) {
			if (input[i].first == INF) {
				break;
			}
			int dc = 0;
			int dc_rank = i;
			for (int ct = 1; ct < consider_n + 1; ct++) {
				int my_rank = 0;
				for (vector<pair<int, int>>::iterator it = rankVector[ct].begin(); it != rankVector[ct].end(); it++) {
					if ((*it).second < input[i].second[ct] && (*it).first != i)
						my_rank++;
					else break;
				}
				if (my_rank < dc_rank) {
					dc_rank = my_rank;
					dc = ct;
				}
			}
			int counter = 0;
			int num_map = rankVector[dc].size();
			vector<int> checkList;
			for (int it = 0; it < rankVector[dc].size(); it++) {
				counter++;
				int key = rankVector[dc][it].first;
				if (key == i) {
					break;
				}
				if (key < i) {
					checkList.push_back(key);
				}
			}
			if (counter > num_map* (1 - 1 / consider_n)) {
				continue;
			}
			int dc_check = 0;
			int non_domi = 0;
			if (checkList.size() == 0) {
				result.push_back(input[i]);
				//cout << "check" << endl;
			}
			else {
				for (int it = 0; it < checkList.size(); it++) {
					int key = checkList[it];

					dc_check++;
					for (int r = 0; r < consider_n; r++) {
						if (input[i].second[r] < input[key].second[r]) {
							non_domi++;
							break;
						}
					}

				}
				if (dc_check == non_domi && dc_check != 0) {
					result.push_back(input[i]);
				}
			}

		}
		return result;
	}

	inline void computeNeigh(int u, vector<int>& neighSlides, vector<vector<pair<int, vector<int>>>>& adjskSlides, vector<pair<int, vector<int>>>& u_sk, vector<int>& b_map) {
		sm->wait();
		judge ju;
		int v;
		vector<pair<int, vector<int>>> uv_sk;
		vector<pair<int, vector<int>>> temp;
		//vector<pair<int, vector<int>>> temp1;
		vector<pair<int, vector<int>>> v_sk;

		unordered_map<int, vector<int>> posInSub;
		unordered_map<int, vector<int>> posInSub_s;
		vector<pair<int, vector<int>>> uv_sk_f;//after pathFiter

		
		for (int pv = 0; pv < neighSlides.size(); pv++) {
			
			v = neighSlides[pv];
			v_sk = adjskSlides[pv];

			if (b_map[v] == b_map[u]) {
				continue;
			}
			else {
				if (u > v) {
					vector<int> ls;
					vector<pair<int, int>> bd;
					if (G.Edge[u][v].size() == 1 && G.Edge[u][v][0].first == INF) {
						uv_sk = concatenation(u_sk, v_sk);
						sort(uv_sk.begin(), uv_sk.end(), ju);
						if (temp.size() > 20000) {
							cout << "large uvsk size: " << uv_sk.size() << endl;
						}
						posInSub = DominationOperator(uv_sk);
						ls = posFilter(posInSub);
						uv_sk_f = pathFilter(uv_sk, ls);
						posInSub_s = updatePIS(posInSub, ls);
						G.Edge[u][v] = uv_sk_f;
						G.Edge[v][u] = uv_sk_f;
						G.EdgeInSub[u][v] = posInSub_s;
						G.EdgeInSub[v][u] = posInSub_s;
					}
					else {
						//continue;
						vector<pair<double, pair<int, vector<int>>>> Block = entropy(G.Edge[u][v], 10);
						uv_sk = concatenation_withCheck(u_sk, v_sk,Block);
						sort(uv_sk.begin(), uv_sk.end(), ju);
						mergeSort(G.Edge[u][v], uv_sk, temp);
						posInSub = DominationOperator(temp);
						ls = posFilter(posInSub);
						uv_sk_f = pathFilter(temp, ls);
						posInSub_s = updatePIS(posInSub, ls);
						G.Edge[u][v] = uv_sk_f;
						G.Edge[v][u] = uv_sk_f;
						G.EdgeInSub[u][v] = posInSub_s;
						G.EdgeInSub[v][u] = posInSub_s;
					}
				}
			}
		}
		sm->notify();
	}
	vector<Node> Tree;
	int root;
	int* belong, * rank;
	int match(int x, vector<int>& neigh) {
		int nearest = neigh[0];
		for (int i = 1; i < neigh.size(); i++)
			if (rank[neigh[i]] > rank[nearest])
				nearest = neigh[i];
		int p = belong[nearest];
		vector<int> a = Tree[p].vert;
		if (Tree[p].uniqueVertex >= 0) {
			a.push_back(Tree[p].uniqueVertex);
		}
		sort(a.begin(), a.end());
		int i, j;
		for (i = 0, j = 0; (i < neigh.size()) && (j < a.size()); ) {
			if (neigh[i] == a[j]) {
				i++; j++;
			}
			else if (neigh[i] < a[j])
				break;
			else j++;
		}
		if (i >= neigh.size()) {
			return p;
		}
		printf("no match!\n");
	}

	void makeTree() {
		belong = (int*)malloc(sizeof(int) * (H.n + 1));
		rank = (int*)malloc(sizeof(int) * (H.n + 1));
		int len = ord.size() - 1;
		Node rootn;
		Tree.clear();
		heightMax = 0;


		int x = ord[len];
		cout << ord.size() << endl;
		rootn.vert = neighbor[x];
		rootn.TPIS = adj_posInSub[x];
		rootn.SK = adj_skyline[x];
		rootn.uniqueVertex = x;
		rootn.pa = -1;
		rootn.height = 1;
		rank[x] = 0;
		belong[x] = 0;
		Tree.push_back(rootn);
		len--;
		for (; len >= 0; len--) {
			int x = ord[len];
			int c = 0;
			Node nod;
			nod.vert = neighbor[x];

			nod.SK = adj_skyline[x];
			nod.TPIS = adj_posInSub[x];
			nod.uniqueVertex = x;
			int pa = match(x, neighbor[x]);
			Tree[pa].ch.push_back(Tree.size());

			nod.pa = pa;
			nod.height = Tree[pa].height + 1;
			if (nod.height > heightMax)
				heightMax = nod.height;
			rank[x] = Tree.size();
			belong[x] = Tree.size();

			Tree.push_back(nod);

		}
		root = 0;
	}

	int* toRMQ;
	vector<int> EulerSeq;
	vector<vector<int>> RMQIndex;
	void makeRMQDFS(int p, int height) {
		toRMQ[p] = EulerSeq.size();
		EulerSeq.push_back(p);
		for (int i = 0; i < Tree[p].ch.size(); i++) {
			makeRMQDFS(Tree[p].ch[i], height + 1);
			EulerSeq.push_back(p);
		}
	}
	void makeRMQ() {
		EulerSeq.clear();
		toRMQ = (int*)malloc(sizeof(int) * (G.n + 1));
		makeRMQDFS(root, 1);
		RMQIndex.clear();
		RMQIndex.push_back(EulerSeq);
		int m = EulerSeq.size();
		for (int i = 2, k = 1; i < m; i = i * 2, k++) {
			vector<int> tmp;
			tmp.clear();
			tmp.resize(EulerSeq.size());
			for (int j = 0; j < m - i; j++) {
				int x = RMQIndex[k - 1][j], y = RMQIndex[k - 1][j + i / 2];
				if (Tree[x].height < Tree[y].height)
					tmp[j] = x;
				else tmp[j] = y;
			}
			RMQIndex.push_back(tmp);
		}
	}
	int LCAQuery(int _p, int _q) {
		int p = toRMQ[_p], q = toRMQ[_q];
		if (p > q) {
			int x = p;
			p = q;
			q = x;
		}
		int len = q - p + 1;
		int i = 1, k = 0;
		while (i * 2 < len) {
			i *= 2;
			k++;
		}
		q = q - i + 1;
		if (Tree[RMQIndex[k][p]].height < Tree[RMQIndex[k][q]].height)
			return RMQIndex[k][p];
		else return RMQIndex[k][q];
	}

	vector<pair<int, vector<int>>> distanceQueryAncestorToPosterity(int p, int q) {
		vector<pair<int, vector<int>>> temp;
		vector<int> tmp_C;
		for (int i = 0; i < consider_n; i++) {
			tmp_C.push_back(0);
		}
		temp.push_back(make_pair(0, tmp_C));
		if (p == q) return temp;
		int x = belong[p], y = belong[q];
		return Tree[y].skyToAnc[Tree[x].pos[Tree[x].pos.size() - 1]];
	}

	void calculateIndexSizeDFS(int p, int pre, int tmp, long long& result) {
		for (int i = 0; i < Tree[p].ch.size(); i++) {
			calculateIndexSizeDFS(Tree[p].ch[i], pre + 1, (pre + 1) + tmp, result);
		}
		if (tmp + (pre + 1) > result) result = tmp + (pre + 1);
	}
	long long calculateIndexSize() {
		long long res = Tree[root].vert.size();
		for (int i = 0; i < Tree[root].ch.size(); i++) {
			calculateIndexSizeDFS(Tree[root].ch[i], Tree[root].vert.size(), Tree[root].vert.size(), res);
		}
		return res;
	}

	void makeIndexDFS_new(int p, vector<int>& list, int* toList) {
		
		judge ju;

		vector<int> C;

		for (int k = 0; k < consider_n; k++) {

			C.push_back(INF);
		}
		Tree[p].pos.resize(Tree[p].vert.size() + 1);
		Tree[p].skyToAnc.resize(list.size());
		Tree[p].TPIS_ANS.resize(list.size());
		for (int i = 0; i < list.size(); i++) {
			Tree[p].skyToAnc[i].resize(list.size());
		}
		//	printf("step1");
		for (int i = 0; i < Tree[p].vert.size(); i++) {
			int j;
			for (j = 0; j < list.size(); j++)
				if (list[j] == Tree[p].vert[i])
					break;
			Tree[p].pos[i] = j;
		}

		Tree[p].pos[Tree[p].vert.size()] = list.size();
		//printf("Step 2");
		pair<int, vector<int>> pp = make_pair(INF, C);
		vector<pair<int, vector<int>>> vp(1, pp);
		Tree[p].skyToAnc.assign(list.size(), vp);

		int x = Tree[p].uniqueVertex;
		vector<vector<int> > vvInput;
		vector<int> vT;
		vvInput.assign(ism2, vT);

		for (int i = 0; i < list.size(); i++)
		{
			for (int j = 0; j < Tree[p].vert.size(); j++)
			{
				int x = Tree[p].vert[j];
				int y = list[i];
				vector<pair<int, vector<int>>> assign;
				vector<pair<int, vector<int>>> assign_s;
				unordered_map<int, vector<int>> assign_pos;
				vector<int> tmp_ls;
				if (x == y)
				{
					assign = Tree[p].SK[j];
					assign_pos = DominationOperator(assign);
					tmp_ls = posFilter(assign_pos);
					assign_s = pathFilter(assign, tmp_ls);
					assign_pos = updatePIS(assign_pos, tmp_ls);
					Tree[p].skyToAnc[toList[x]] = assign_s;
					Tree[p].TPIS_ANS[toList[x]] = assign_pos;
					continue;
				}
			}
		}


		for (int i = 0; i < list.size(); i++) {
			vvInput[i % ism2].push_back(list[i]);
		}

		cout << "Tree " << p << "\t width:" << Tree[p].pos.size() << endl;
		vector<vector<pair<int, vector<int>> > > vvpSkyline;
		for (int i = 0; i < Tree[p].vert.size(); i++)
		{
			int x = Tree[p].vert[i];
			vvpSkyline.push_back(Tree[p].SK[i]);
		}
		boost::thread_group threads;
		for (int i = 0; i < ism2; i++)
		{
			if (!vvInput[i].empty())
			{
				threads.add_thread(new boost::thread(&Bound_Tree_Decomposition::propagation, this, p, boost::ref(vvInput[i]), boost::ref(toList), list.size(), boost::ref(list), boost::ref(vvpSkyline), boost::ref(b_map)));

			}
		}
		threads.join_all();
		//printf("Step 4");
		toList[Tree[p].uniqueVertex] = list.size();
		list.push_back(Tree[p].uniqueVertex);
		for (int i = 0; i < Tree[p].ch.size(); i++) {
			makeIndexDFS_new(Tree[p].ch[i], list, toList);
		}
		list.pop_back();

		sort(Tree[p].pos.begin(), Tree[p].pos.end());
	}


	unordered_map<int, vector<int>> posQueryAncestorToPosterity(int p, int q) {
		unordered_map<int, vector<int>> tmp;
		tmp = IPOS();
		if (p == q) return tmp;
		int x = belong[p], y = belong[q];
		return Tree[y].TPIS_ANS[Tree[x].pos[Tree[x].pos.size() - 1]];
	}


	inline vector<int> cube(vector<vector<pair<int, vector<int>>>>& x, vector<vector<pair<int, vector<int>>>>& y, vector<int>& p) {
		int bbxMin, bbyMin, bbxMax, bbyMax;
		vector<int> res;
		vector<vector<pair<int, vector<int>>>> hops;
		vector<pair<int, vector<int>>> upperleft;
		vector<pair<int, vector<int>>> downright;

		judge ju;
		vectJudge2 vJu;
		hops.resize(p.size());
		if (p.size() == 1) {
			res.push_back(0);
			return res;
		}
		vector<vector<int>> lowbound_x;
		vector<vector<int>> highbound_x;
		vector<vector<int>> lowbound_y;
		vector<vector<int>> highbound_y;

		lowbound_x.resize(p.size());
		lowbound_y.resize(p.size());
		highbound_x.resize(p.size());
		highbound_y.resize(p.size());

		vector<vector<int>> lowbound;
		vector<vector<int>> highbound;
		lowbound.resize(p.size());
		highbound.resize(p.size());

		vector<vector<int>> d_min_x;
		vector<vector<int>> d_min_y;
		vector<vector<int>> d_max_x;
		vector<vector<int>> d_max_y;
		d_min_x.resize(consider_n);
		d_min_y.resize(consider_n);
		d_max_x.resize(consider_n);
		d_max_y.resize(consider_n);
		//cout << "check1" << endl;
		for (int i = 0; i < p.size(); ++i) {
			d_min_x.clear();
			d_min_y.clear();
			d_max_x.clear();
			d_max_y.clear();

			for (int z = 0; z < consider_n; z++) {
				vector<int> tmp_sortV;
				for (int j = 0; j < x[p[i]].size(); ++j) {
					tmp_sortV.push_back(x[p[i]][j].second[z]);
				}
				sort(tmp_sortV.begin(), tmp_sortV.end(), vJu);
				d_min_x[z].push_back(tmp_sortV[0]);
				d_max_x[z].push_back(tmp_sortV[tmp_sortV.size() - 1]);
			}
			for (int it = 0; it < consider_n; it++) {
				lowbound_x[i].push_back(d_min_x[it][0]);
				highbound_x[i].push_back(d_max_x[it][0]);
			}

			for (int z = 0; z < consider_n; z++) {
				vector<int> tmp_sortV;
				for (int j = 0; j < y[p[i]].size(); ++j) {
					tmp_sortV.push_back(y[p[i]][j].second[z]);
				}
				sort(tmp_sortV.begin(), tmp_sortV.end(), vJu);
				d_min_y[z].push_back(tmp_sortV[0]);
				d_max_y[z].push_back(tmp_sortV[tmp_sortV.size() - 1]);
			}
			for (int it = 0; it < consider_n; it++) {
				lowbound_y[i].push_back(d_min_y[it][0]);
				highbound_y[i].push_back(d_max_y[it][0]);
			}
		}
		for (int i = 0; i < p.size(); ++i) {
			lowbound[i].push_back(x[p[i]][0].first + y[p[i]][0].first);
			highbound[i].push_back(x[p[i]][x[p[i]].size() - 1].first + y[p[i]][y[p[i]].size() - 1].first);
			for (int j = 0; j < consider_n; ++j) {
				int tmp_low = lowbound_x[i][j] + lowbound_y[i][j];
				int tmp_high = highbound_x[i][j] + highbound_y[i][j];
				lowbound[i].push_back(tmp_low);
				highbound[i].push_back(tmp_high);
			}
		}
		vector<int> deleteList;
		for (int i = 0; i < p.size() - 1; ++i) {
			int counter = 0;
			int _counter = 0;

			int size_d = deleteList.size();
			if (size_d > 0) {
				bool check = false;
				for (int j = 0; j < size_d; j++) {
					if (i == deleteList[j]) {
						check = true;
					}
				}
				if (check) {
					continue;
				}
			}
			for (int j = i + 1; j < p.size(); ++j) {
				for (int k = 0; k < consider_n + 1; k++) {
					if (highbound[i][k] <= lowbound[j][k]) {
						counter++;
					}
					if (lowbound[i][k] >= highbound[j][k]) {
						_counter++;
					}
				}
				if (counter == consider_n + 1) {
					deleteList.push_back(j);
				}
				if (_counter == consider_n + 1) {
					deleteList.push_back(i);
					break;
				}
			}
		}
		for (int i = 0; i < p.size(); i++) {
			vector<int>::iterator it;
			it = std::find(deleteList.begin(), deleteList.end(), i);
			if (it == deleteList.end()) {
				res.push_back(i);
			}
		}
		return res;
	}

	void propagation(int p, vector<int>& list, int* toList, int ancNum, vector<int>& ancList, vector<vector<pair<int, vector<int>>>>& vvpSkyline, vector<int>& b_map) {
		sm2->wait();
		vector<pair<int, vector<int>>> z;
		unordered_map<int, vector<int>> po;
		vector<pair<int, vector<int>>> _z;
		vector<pair<int, vector<int>>> zz_s;
		unordered_map<int, vector<int>> posInSub;
		vector<int> ls;
		vector<vector<int>> hpList;


		vector<pair<int, vector<int>>> assign;
		vector<pair<int, vector<int>>> assign_s;
		unordered_map<int, vector<int>> assign_pos;


		vector<vector<vector<pair<int, vector<int>>>>> H1;

		vector<vector<vector<pair<int, vector<int>>>>> H2;

		vector<int> tmp_ls;

		for (int i = 0; i < list.size(); i++)
		{
			for (int j = 0; j < Tree[p].vert.size(); j++)
			{
				int x = Tree[p].vert[j];
				int y = list[i];

				if (x == y)
				{
					mergeSort(vvpSkyline[j], Tree[p].SK[j], assign);
					assign_pos = DominationOperator(assign);
					tmp_ls = posFilter(assign_pos);
					assign_s = pathFilter(assign, tmp_ls);
					assign_pos = updatePIS(assign_pos, tmp_ls);
					Tree[p].skyToAnc[toList[x]] = assign_s;
					Tree[p].TPIS_ANS[toList[x]] = assign_pos;
					continue;
				}
			}
		}

		if (Tree[p].vert.size() < 8) {
			for (int i = 0; i < list.size(); i++)
			{

				int y = list[i];
				int tp = Tree[p].uniqueVertex;
				if (b_map[y] == b_map[tp]) {

					continue;
				}
				for (int j = 0; j < Tree[p].vert.size(); j++)
				{
					int x = Tree[p].vert[j];
					vector<pair<int, vector<int>>> zz;

					if (x == y)
					{
						if (b_map[x] == b_map[Tree[p].uniqueVertex]) {
							continue;
						}
						else {
							mergeSort(vvpSkyline[j], Tree[p].SK[j], assign);
							assign_pos = DominationOperator(assign);
							tmp_ls = posFilter(assign_pos);
							assign_s = pathFilter(assign, tmp_ls);
							assign_pos = updatePIS(assign_pos, tmp_ls);
							Tree[p].skyToAnc[toList[x]] = assign_s;
							Tree[p].TPIS_ANS[toList[x]] = assign_pos;
						}
						continue;
					}
					int ix, iy;
					for (int k = 0; k < ancList.size(); k++)
					{
						if (ancList[k] == x)
							ix = k;
						if (ancList[k] == y)
							iy = k;
					}

					if (ix < iy)
					{
						z = distanceQueryAncestorToPosterity(x, y);
					}
					else
					{
						z = distanceQueryAncestorToPosterity(y, x);
					}
					
					vector<pair<double, pair<int, vector<int>>>> Block = entropy(Tree[p].skyToAnc[toList[y]], 10);
					_z = concatenation_withCheck(z, vvpSkyline[j], Block);		
					mergeSort(_z, Tree[p].skyToAnc[toList[y]], zz);
					posInSub = DominationOperator(zz);
					ls = posFilter(posInSub);
					zz_s = pathFilter(zz, ls);
					posInSub = updatePIS(posInSub, ls);
					Tree[p].skyToAnc[toList[y]] = zz_s;
					Tree[p].TPIS_ANS[toList[y]] = posInSub;
				}
			}
		}
		else {
			for (int i = 0; i < list.size(); i++)
			{
				if (list.size() > 0) {
					vector<int> p_set;
					vector<int> hp;
					vector<vector<pair<int, vector<int>>>> h1;
					vector<vector<pair<int, vector<int>>>> h2;
					int y = list[i];
					int tp = Tree[p].uniqueVertex;
					if (b_map[y] == b_map[tp]) {

						continue;
					}

					for (int j = 0; j < Tree[p].vert.size(); j++) {
						int x = Tree[p].vert[j];

						int ix, iy;
						for (int k = 0; k < ancList.size(); k++)
						{
							if (ancList[k] == x)
								ix = k;
							if (ancList[k] == y)
								iy = k;
						}

						if (ix < iy)
						{
							z = distanceQueryAncestorToPosterity(x, y);

						}
						else
						{
							z = distanceQueryAncestorToPosterity(y, x);

						}
						h1.push_back(z);
						h2.push_back(vvpSkyline[j]);
						p_set.push_back(j);
					}
					H1.push_back(h1);
					H2.push_back(h2);
					hp = cube(h1, h2, p_set);
					hpList.push_back(hp);
				}
			}

			//	cout << "Merging" << endl;
			for (int i = 0; i < list.size(); i++) {
				int tp = Tree[p].uniqueVertex;
				int y = list[i];
				for (int j = 0; j < Tree[p].vert.size(); j++)
				{
					int x = Tree[p].vert[j];

					if (x == y)
					{
						if (b_map[x] == b_map[tp]) {
							continue;
						}
						mergeSort(vvpSkyline[j], Tree[p].SK[j], assign);
						assign_pos = DominationOperator(assign);
						tmp_ls = posFilter(assign_pos);
						assign_s = pathFilter(assign, tmp_ls);
						assign_pos = updatePIS(assign_pos, tmp_ls);

						Tree[p].skyToAnc[toList[x]] = assign_s;
						Tree[p].TPIS_ANS[toList[x]] = assign_pos;
						continue;
					}
				}
			}

			//	cout << "Concatenating" << endl;
			for (int i = 0; i < list.size(); i++) {
				int tp = Tree[p].uniqueVertex;
				int y = list[i];
				if (b_map[y] == b_map[tp]) {
					continue;
				}
				vector<pair<int, vector<int>>> zz;
				unordered_map<int, vector<int>> hopInSub;
				vector<int> hp;
				hp = hpList[i];
				for (int vi = 0; vi < hp.size(); vi++) {
					vector<pair<double, pair<int, vector<int>>>> Block = entropy(Tree[p].skyToAnc[toList[y]], 10);
					_z = concatenation_withCheck(H1[i][hp[vi]], H2[i][hp[vi]], Block);
					mergeSort(_z, Tree[p].skyToAnc[toList[y]], zz);
					posInSub = DominationOperator(zz);
					ls = posFilter(posInSub);
					zz_s = pathFilter(zz, ls);
					posInSub = updatePIS(posInSub, ls);
					Tree[p].skyToAnc[toList[y]] = zz_s;
					Tree[p].TPIS_ANS[toList[y]] = posInSub;
				}
			}
		}
		sm2->notify();
	}


	void makeIndex() {
		makeRMQ();

		//H.EdgeInitialize();

		//printCSPCHIndex();

	}

	void readPositionIndex(string file, vector<vector<int>>& position) {
		ifstream in(file);
		string line;
		vector<int> temp;
		while (getline(in, line)) {
			stringstream ss(line);
			int x;
			while (ss >> x) {
				//cout << x << '\t';
				temp.push_back(x);
			}
			position.push_back(temp);
			temp.clear();
			//cout << endl;
		}
		in.close();
	}

	void readSkylineIndex(string file) {
		ifstream in(file);
		int n, ns, vert, sks;
		vector<int> C;
		for (; in >> n >> ns >> vert >> sks;) {
			Tree[n].skyToAnc.resize(ns);
			for (int i = 0; i < sks; i++) {
				int x, y;
				in >> x;
				C.clear();
				for (int k = 0; k < consider_n; k++) {
					in >> y;
					C.push_back(y);
				}
				Tree[n].skyToAnc[vert].push_back(make_pair(x, C));
			}
		}
		in.close();
	}


#if 0
	void printCSPCHIndex() {
		ofstream outfile;
		outfile.open("order_index(NY_R).txt");
		for (int i = 0; i < ord.size(); i++) {
			outfile << i << '\t' << ord[i] << endl;
		}
		outfile.close();

		ofstream outfile1;
		outfile1.open("CSPCH_index(NY_R).txt");
		for (int i = 0; i < Tree.size(); i++) {
			//outfile1 << i << '\t';
			for (int j = 0; j < Tree[i].SK.size(); j++) {
				outfile1 << Tree[i].uniqueVertex << '\t' << Tree[i].SK.size() << '\t' << Tree[i].vert[j] << '\t' << Tree[i].SK[j].size() << '\t';
				for (int k = 0; k < Tree[i].SK[j].size(); k++) {
					outfile1 << Tree[i].SK[j][k].first << '\t';
					for (int p = 0; p < consider_n; p++) {
						outfile1 << Tree[i].SK[j][k].second[p] << '\t';
					}
				}
				outfile1 << endl;
			}
		}
		outfile1.close();
	}
#endif

	void printIndex() {
		ofstream outfile;
		outfile.open("FHL_Index/position_index(bound).txt");
		for (int i = 0; i < Tree.size(); i++) {
			if (Tree[i].pos.size() > 9999) {
				Tree[i].pos.clear();
				continue;
			}
			for (int j = 0; j < Tree[i].pos.size(); j++) {
				outfile << Tree[i].pos[j] << '\t';
			}
			outfile << endl;
		}
		outfile.close();

		ofstream outfile1;
		outfile1.open("FHL_Index/skyline_index(bound).txt");
		for (int i = 0; i < Tree.size(); i++) {
			//outfile1 << i << '\t';
			for (int j = 0; j < Tree[i].skyToAnc.size(); j++) {
				outfile1 << i << '\t' << Tree[i].skyToAnc.size() << '\t' << j << '\t' << Tree[i].skyToAnc[j].size() << '\t';
				for (int k = 0; k < Tree[i].skyToAnc[j].size(); k++) {
					outfile1 << Tree[i].skyToAnc[j][k].first << '\t';
					for (int p = 0; p < consider_n; p++) {
						outfile1 << Tree[i].skyToAnc[j][k].second[p] << '\t';
					}
				}
				outfile1 << endl;
			}
		}
		outfile1.close();
	}

	void loadIndex(int a) {
		if (a == 0) {
			cout << "Re-building CSP-2Hop index" << endl;

			std::chrono::high_resolution_clock::time_point t1;
			std::chrono::high_resolution_clock::time_point t2;
			std::chrono::duration<double> time_span;

			t1 = std::chrono::high_resolution_clock::now();
			makeIndex3();
			reducePos();
			t2 = std::chrono::high_resolution_clock::now();
			time_span = std::chrono::duration_cast<std::chrono::duration<double>>(t2 - t1);
			cout << "Boundary Tree Time:" << time_span.count() << endl;

			printIndex();
		}
		else {
			cout << "Loading CSP-2Hop index" << endl;
			vector<vector<int>> ps;
			char positionFile[255] = "FHL_Index/position_index(bound).txt";
			char skylineFile[255] = "FHL_Index/skyline_index(bound).txt";
			readPositionIndex(positionFile, ps);
			for (int i = 0; i < ps.size(); i++) {
				Tree[i].pos = ps[i];
			}
			readSkylineIndex(skylineFile);
		}
	}


	void makeIndex3() {
		vector<int> list;
		list.clear();
		int* toList;
		toList = (int*)malloc(sizeof(int) * (G.n + 1));
		Tree[root].pos.clear();

		toList[Tree[root].uniqueVertex] = 0;
		list.push_back(Tree[root].uniqueVertex);
		Tree[root].pos.push_back(0);

		for (int i = 0; i < Tree[root].ch.size(); ++i) {
			makeIndexDFS_new(Tree[root].ch[i], list, toList);
			break;
		}
		free(toList);

	}

	void reducePosDFS(int p) {
		if (Tree[p].ch.size() == 2) {
			int t = Tree[p].ch[0];
			if (Tree[Tree[p].ch[0]].pos.size() > Tree[Tree[p].ch[1]].pos.size())
				t = Tree[p].ch[1];
			Tree[p].pos = Tree[t].pos;
			Tree[p].pos.erase(Tree[p].pos.begin() + (Tree[p].pos.size() - 1));
		}
		for (int i = 0; i < Tree[p].ch.size(); i++)
			reducePosDFS(Tree[p].ch[i]);
	}
	void reducePos() {
		reducePosDFS(root);
	}
	void cntSize() {
		long long s_nonroot = 0;
		long long s_size = 0;

		long long s_dis = 0;
		for (int i = 0; i < Tree.size(); ++i) {
			s_nonroot += Tree[i].height - 1;
			s_size += Tree[i].vert.size();
			s_dis += Tree[i].height;
		}
		long long s_root = (long long)Tree[0].vert.size() * (long long)G.n;
		printf("tree width: %d\n", tree_width);
		printf("nonroot idx size = %0.3lfGB, avg node size=%0.3lf, avg label size=%0.3lf\n",
			s_nonroot * 4.0 / 1000000000.0, s_size * 1.0 / G.n, s_dis * 1.0 / G.n);
	}

};
void constructSubTree(int i, vector<Sub_Tree_Decomposition>& TDs)
{
	sm3->wait();
	cout << "Sub_Tree: " << i << endl;
	Sub_Tree_Decomposition td;
	string bb = "";
	bb = to_string(static_cast<long long>(i));
	string str = "sp/sp.txt" + bb;
	str = str + ".txt";
	cout << str << endl;
	char graphFileName[255] = "sampleGraph.txt";
	char* data_name = (char*)str.c_str();
	Graph G = Graph(graphFileName, data_name, i, 0);
	td.G = G;
	td.H = td.G;
	cout << "reduce..." << endl;
	td.reduce(i);
	cout << "make tree..." << endl;
	td.makeTree();
	td.makeIndex();
	td.loadIndex(0, i);//input 0 for re-building index, input 10 for re-building index (optimal), input 1 for reading index existed

	td.cntSize();
	TDs[i] = td;
	cout << VMap.size() << endl;
	sm3->notify();
}

int main(int argc, char* argv[])
{
	VMap.resize(All_v+1);
	vector<Sub_Tree_Decomposition> TDs;
	char graphFileName[255] = "sampleGraph.txt";
	Sub_Tree_Decomposition td;
	TDs.assign(fn, td);
	std::chrono::high_resolution_clock::time_point t1;
	std::chrono::high_resolution_clock::time_point t2;
	std::chrono::duration<double> time_span;

	boost::thread_group threads;

	t1 = std::chrono::high_resolution_clock::now();
	for (int i = 0; i < fn; i++)
	{
		threads.add_thread(new boost::thread(&constructSubTree, i, boost::ref(TDs)));
		//constructSubTree(i, TDs);
	}
	threads.join_all();

	t2 = std::chrono::high_resolution_clock::now();
	time_span = std::chrono::duration_cast<std::chrono::duration<double>>(t2 - t1);
	cout << "Small Tree Totol building: " << time_span.count() << endl;
	
	cout << "Bound_Tree" << endl;
	Bound_Tree_Decomposition btd;
	string str_bound = "bound.txt";
	char* data_name_bound = (char*)str_bound.c_str();
	Graph bG = Graph(graphFileName, data_name_bound, fn, 1);
	cout << "Graph Readed" << endl;
	btd.G = bG;
	btd.H = btd.G;
	btd.TDs = TDs;
	auto start = system_clock::now();
	cout << "reduce..." << endl;

	t1 = std::chrono::high_resolution_clock::now();
	btd.reduce();
	cout << "make tree..." << endl;
	btd.makeTree();
	cout << "make index..." << endl;
	btd.makeIndex();
	t2 = std::chrono::high_resolution_clock::now();
	time_span = std::chrono::duration_cast<std::chrono::duration<double>>(t2 - t1);
	cout << "Boundary Tree building: " << time_span.count() << endl;
	btd.loadIndex(0);//input 0 for re-building index, input 10 for re-building index (optimal), input 1 for reading index existed
	btd.cntSize();
	auto end = system_clock::now();
	auto duration = duration_cast<microseconds>(end - start);
	double time = double(duration.count()) * microseconds::period::num / microseconds::period::den;
	cout << "indexing time:" << time << endl;
	cout << "indexing complete!" << endl;
	return 0;

}