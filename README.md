# verifaps-maven-parent

Parent POM for Verifaps Projects

## How to use

Add following into your `pom.xml`:

```
<project>
    ...
    <parent>
        <groupId>edu.kit.iti.formal</groupId>
        <artifactId>verifaps</artifactId>
        <version>1.2.0</version>
    </parent>

    <repositories>
        <repository>
            <id>institute</id>
            <url>http://formal.iti.kit.edu/</url>
        </repository>
    </repositories>
    ...
</project>
```


## Features and Settings

* Plugins
  * Checkstyle
  * FindBugs
  * License Plugin
    * Default License: `${license.identifier}` (gpl_v3)
    * inceptionYear: `${license.inceptionYear}`  (2016)
    * copyrightOwners: `${license.copyrightOwner}` (Alexander Weigl)
* Repositories:
  * http://formal.iti.kit.edu/
* Dependencies
  * `junit:junit:4.12`


## Useful Commands

* Deploy to local folder:


  ```
  mvn -DperformRelease=true [-DskipTests=true] deploy
  ```

* Generate and deploy website:

  ```
  mvn site:site site:deploy
  ```

* Update license headers:

  ```
  mvn license:update-file-header
  ```

  *You should commit before executing*

* Fix JavaDoc
  ```
  mvn javadoc:fix
  ```
  *You should commit before executing*


## Changelog

### 1.2.0

* Add JXR 
* Add Surefire Reports

### 1.1.0

* Introduce `${local.deploy.site}` and `${local.deploy.repository}` properties.

### 1.0.0

* Initial version




## Authors

* Alexander Weigl <weigl@kit.edu>





<!-- Local Variables: -->
<!-- ispell-dictionary: "english" -->
<!-- End: -->
