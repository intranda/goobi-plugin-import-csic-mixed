package de.intranda.goobi.plugins;

import java.io.File;
import java.util.ArrayList;
import java.util.List;

public class VolumeInfo {
	public String identifier;
	public String pieceDesignation;
	public int volumeNumber;
	public int totalVolumes;
	public List<File> imageDirs;
	public List<File> pdfFiles;
	public String identifierSuffix;
	public String projectName;
	
	public VolumeInfo(String identifier, int volumeNumber, int totalVolumes, String pieceDesignation, List<File> imageDirs, List<File> pdfFiles, String identifierSuffix, String projectName) {
		this.identifier = identifier;
		this.pieceDesignation = pieceDesignation;
		this.volumeNumber = volumeNumber;
		this.totalVolumes = totalVolumes;
		this.imageDirs = imageDirs;
		this.identifierSuffix = identifierSuffix;
		this.projectName = projectName;
		this.pdfFiles = pdfFiles;
	}
	
	   public VolumeInfo(String identifier, int volumeNumber, int totalVolumes, String pieceDesignation, File imageDir, File pdfFile, String identifierSuffix, String projectName) {
	        this.identifier = identifier;
	        this.pieceDesignation = pieceDesignation;
	        this.volumeNumber = volumeNumber;
	        this.totalVolumes = totalVolumes;
	        this.imageDirs = new ArrayList<File>();
	        this.imageDirs.add(imageDir);
	        this.identifierSuffix = identifierSuffix;
	        this.projectName = projectName;
	        this.pdfFiles = new ArrayList<File>();
	        this.pdfFiles.add(pdfFile);
	    }
	
}
