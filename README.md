# FHL_Cube
1. Install **Boost C++ Libraries**.
2. Decompress _sampleGraph.txt.zip_ and _sampleBoundData_2DSky.zip_ (in the folder sampleBoundData) for running the code on the sample road network.
3. The parameters in code have been preset for running the sample road network.
4. Before run the code, please check the description of the parameters, and ensure the setting for data is correct.
   - Please re-set **PARAMETERs** below if the graph is changed.
     - **sm**: The number of threads on index contraction.
     - **sm2**: The number of threads on propagation.
     - **sm3**: The number of threads on small trees index construction.
     - **ism1**: Set its value as the same as **sm**.
     - **ism2**: Set its value as the same as **sm2**.
     - **fn**: The number of partitions (re-set it if the number of partitions is changed).
     - **All_v**: The number of vertices in the road network.
     - **fullspace**: The total number of dimensions of the road network.
     - **subgraphBound**: The path of the folder: sampleBoundData/sampleBoundData_SubBound.
       - _NOTE: It needs to save the boundary vertices in every partition._
     - **sub_bound_skylines**: The path of the folder: sampleBoundData/sampleBoundData_2DSky.
       - _NOTE: It needs to save the skyline paths from boundary vertices to boundary vertices.The folder sampleBoundData only provides the skyline paths in all the 2d subspaces. Please use the complete skyline paths for testing the real performance._
5. makefile: Run the command **make** to compile and run the code.
