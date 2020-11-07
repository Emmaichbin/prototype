Usage of the Prototype:

1. To get the prototype work, first you need to make sure you have Java Runtime Environment installed on your machine, and we suggest you using an Java IDE such as Eclipse to run the program.

2. Download the source code, together with other files, and import it as a Java project into your IDE.

3. To run the logical difference computation method, go to the directory "Forgetting" and run the main method in LDiff.java. Consider the task of computing the UI-based logical difference UI-Diff(T1, T2) between two ELH-TBoxes T1 and T2: the input are T1, T2 and a path specifying the location where you want the output (a set of witnesses) to be saved; see the following example.<br/>
T1:
file:///C:/Users/XXXXX/Desktop/snomed_ct/snomed_ct_interntional/ontology_201701.owl<br/>
T2:
file:///C:/Users/XXXXX/Desktop/snomed_ct/snomed_ct_interntional/ontology_201707.owl<br/>
Path: 
file:///C:/Users/XXXXX/Desktop/snomed_ct/<br/>

4. To run the uniform interpolation method, go to the directory "Swing" and run the main method in GUI.java to call a GUI pop up, where you could load the target ontology by cliking the "Load Ontology" button, and specify the concept/role names you want to forget, click the "Forget" button you will see the uniform interpolant computed by the system. You could save the result locally as an .owl file by clicking the "Save Ontology" button.


### For Developer
Requirements:
1. Gradle 6 or above
2. JDK 1.8 
```
git clone https://github.com/anonymous-ai-researcher/prototype.git
cd prototype
gradlew.bat run (for Linux run: ./gradlew run)
```
