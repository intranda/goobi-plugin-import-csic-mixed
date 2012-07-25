package de.intranda.goobi.plugins;

import java.io.File;

public class VolumeInfo {
	public int volumeNumber;
	public int totalVolumes;
	public File imageDir;
	public String identifierSuffix;
	public String projectName;
	
	public VolumeInfo(int volumeNumber, int totalVolumes, File imageDir, String identifierSuffix, String projectName) {
		this.volumeNumber = volumeNumber;
		this.totalVolumes = totalVolumes;
		this.imageDir = imageDir;
		this.identifierSuffix = identifierSuffix;
		this.projectName = projectName;
	}
	
	
}
