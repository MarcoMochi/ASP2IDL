# ASP2IDL

ASP2IDL allows the translation of grounded ASP programs into Difference Logic. 

ASP2IDL can be used with: 

```python main.py -i input_file [-o output] [-aspif] [-scc path_SCC] ```

Where input_file is the path to the grounded ASP program, that can be in "--text" format or in the ASPIF format, in that case, the option "-aspif" must be used. Moreover, a path to the file containing the SCCs can be given to the tool, allowing the usage of the SCC optimization. In that case, the option "-scc" must be used followed by the path to the SCC file.

To obtain the SCC file you can use the following command:

```gringo input_file --output=reify --reify-sccs | clingo - Get_sccs.lp > path_SCC```

This command uses the Get_sccs.lp file in the repository and creates the file with the information on the SCCs used to deploy the optimizations. 

The repository contains two folders with the instances used for testing the ASP2IDL tool:
- Inside the "input" folder there are 5 subfolders, each for every used domain, containing two subfolders. One subfolder "Aspif" contains the grounded instances in the aspif format, and the "Scc" contains the sccs files. In case of tight domains, the "Scc" folder contains just a single empty file that should be used to deploy the optimizations.  
- Inside the translations subfolder there are 5 subfolders, each for every used domain, containing two subfolders, one "ASP2IDL" containing the translations obtained without the SCC optimization and "ASP2IDL + SCCs" for the translations with the SCC optimization. 
