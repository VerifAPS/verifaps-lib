package edu.kit.iti.formal.automation;

import lombok.Value;

@Value
public class Version {
    public String version = "$version";
    public String lastTag = "$lastTag";
    public String commitDistance = "$commitDistance";
    public String hash = "$hash";
    public String hashFull = "$hashFull";
    public String branchName = "$branchName";
    public boolean isClean = $isClean;
    public String buildTime = "$buildTime";
}