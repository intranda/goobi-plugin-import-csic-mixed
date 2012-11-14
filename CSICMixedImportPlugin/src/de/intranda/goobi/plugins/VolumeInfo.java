package de.intranda.goobi.plugins;

import java.io.File;

public class VolumeInfo {
	public String identifier;
	public String pieceDesignation;
	public int volumeNumber;
	public int totalVolumes;
	public File imageDir;
	public File pdfFile;
	public String identifierSuffix;
	public String projectName;
	
	public VolumeInfo(String identifier, int volumeNumber, int totalVolumes, String pieceDesignation, File imageDir, File pdfFile, String identifierSuffix, String projectName) {
		this.identifier = identifier;
		this.pieceDesignation = pieceDesignation;
		this.volumeNumber = volumeNumber;
		this.totalVolumes = totalVolumes;
		this.imageDir = imageDir;
		this.identifierSuffix = identifierSuffix;
		this.projectName = projectName;
		this.pdfFile = pdfFile;
	}
	
	
}
