CXX=g++ -std=c++17
OPT=-O3

CSP: fhl_cube.o -lboost_system -lboost_thread
	$(CXX) -g fhl_cube.o -lboost_system -lboost_thread

fhl_cube.o:fhl_cube.cpp
	$(CXX) -g -c $(OPT) fhl_cube.cpp 

clean:
	rm *.o
	rm a.out
