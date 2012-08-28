/*************************************************************************
 * 
 * Copyright intranda GmbH
 * 
 * ************************* CONFIDENTIAL ********************************
 * 
 * [2003] - [2012] intranda GmbH, Bertha-von-Suttner-Str. 9 , 37085 Göttingen, Germany
 * 
 * All Rights Reserved.
 * 
 * NOTICE: All information contained herein is protected by copyright. 
 * The source code contained herein is proprietary of intranda GmbH. 
 * The dissemination, reproduction, distribution or modification of 
 * this source code, without prior written permission from intranda GmbH, 
 * is expressly forbidden and a violation of international copyright law.
 * 
 *************************************************************************/
package de.intranda.goobi.plugins;

import java.io.File;
import java.io.FileOutputStream;
import java.io.FilenameFilter;
import java.io.IOException;
import java.io.OutputStreamWriter;
import java.io.Writer;
import java.text.DecimalFormat;
import java.util.ArrayList;
import java.util.List;

import org.apache.log4j.Logger;
import org.apache.pdfbox.pdmodel.PDDocument;
import org.apache.pdfbox.util.PDFTextStripper;

import com.lowagie.text.Document;
import com.lowagie.text.DocumentException;
import com.lowagie.text.pdf.BadPdfFormatException;
import com.lowagie.text.pdf.PdfCopy;
import com.lowagie.text.pdf.PdfImportedPage;
import com.lowagie.text.pdf.PdfReader;



/**
 * Splits a pdf file into pages ande extracts full text files for each
 * 
 * @author florian
 * 
 */
public class PdfExtractor {

	private static final Logger logger = Logger.getLogger(PdfExtractor.class);
	private static final DecimalFormat filenameFormat = new DecimalFormat("00000000");

	private int pdfPageCounter = 1;
	private String encoding = "utf-8";

	public boolean extractPdfs(File importFile, File outputPdfDir, File outputTextDir) {

		boolean success = true;
		
		ArrayList<File> pdfOutputFiles = new ArrayList<File>();
		if (!splitPdfFile(importFile, outputPdfDir, pdfOutputFiles)) {
			return false;
		}

		logger.info("Moving " + pdfOutputFiles.size() + " pdf files and extracting plain text files");
		for (File file : pdfOutputFiles) {
			try {
				if (outputTextDir != null) {
					// creating plain text files
					if (!writeFullText(file, outputTextDir)) {
						logger.error("Error creating plaintext file from pdf. ");
						success = false;
						break;
					}
				}
				// renaming pdf files goobi format
				File destFile = new File(outputPdfDir, getNewFilename(file.getName()));
				logger.debug("Renaming " + file.getAbsolutePath() + " to " + destFile.getAbsolutePath());
				file.renameTo(destFile);
			} catch (IOException e) {
				logger.error("Error creating plaintext file from pdf: " + e.toString());
				success = false;
				break;
			}
		}

		if (!success) {
			if (pdfOutputFiles != null) {
				for (File file : pdfOutputFiles) {
					if (file != null && file.isFile()) {
						file.delete();
					}
				}
			}
			return false;
		}

		logger.info("Done with pdf files");
		return true;
	}

	private boolean splitPdfFile(File file, File destFolder, List<File> destFileList) {
		PdfReader reader = null;
		try {
			reader = new PdfReader(file.getAbsolutePath());
		} catch (IOException e) {
			logger.error("Error opening pdf file " + file.getName());
			return false;
		}
		int pageCount = reader.getNumberOfPages();
		logger.debug("Found " + pageCount + " pages in pdf file");
		String errorString = "Error extracting pdf";
		for (int i = 0; i < pageCount; i++) {
			Document document = null;
			PdfCopy writer = null;
			try {
				errorString += " " + i + ": ";
				String outFileName = file.getName().substring(0, file.getName().toLowerCase().indexOf(".pdf")) + "_" + String.format("%04d", pdfPageCounter++)
						+ ".pdf";
				logger.debug("Creating new pdf file " + outFileName);
				File outFile = new File(destFolder, outFileName);
				document = new Document(reader.getPageSizeWithRotation(1));
				writer = new PdfCopy(document, new FileOutputStream(outFile));
				document.open();
				PdfImportedPage page = writer.getImportedPage(reader, i + 1);
				writer.addPage(page);
				document.close();
				writer.close();
				destFileList.add(outFile);
			} catch (IOException e) {
				logger.error(errorString + e.toString());
				return false;
			} catch (BadPdfFormatException e) {
				logger.error(errorString + e.toString());
				return false;
			} catch (DocumentException e) {
				logger.error(errorString + e.toString());
				return false;
			} finally {
				if (document != null)
					document.close();
				if (writer != null)
					writer.close();
			}
		}
		if (reader != null)
			reader.close();
		return true;
	}

	private boolean writeFullText(File docFile, File textDir) throws IOException {
		PDDocument doc = PDDocument.load(docFile);

		if (doc == null) {
			logger.error("PDF document is null.");
			return false;
		}

		try {
			PDFTextStripper stripper = new PDFTextStripper();
			if (!textDir.exists()) {
				textDir.mkdirs();
			}

			logger.debug("Extracting " + doc.getNumberOfPages() + " full text pages...");
			int i = 0;
			for (; i <= doc.getNumberOfPages(); ++i) {
				stripper.setStartPage(i);
				stripper.setEndPage(i);
				String filename = getNewFilename(docFile.getName());
				filename = filename.substring(0, filename.lastIndexOf("."));
				if (doc.getNumberOfPages() > 1) {
					filename += ("-" + String.format("%03d", i));
				}
				filename += ".txt";
				File plainTextFile = new File(textDir, filename);
				Writer writer = new OutputStreamWriter(new FileOutputStream(plainTextFile), encoding);
				stripper.writeText(doc, writer);
				writer.close();
			}
			logger.debug(i + " text files extracted.");
		} catch (IOException e) {
			logger.error(e.toString());
			return false;
		} finally {
			doc.close();
		}

		return true;
	}

	private String getNewFilename(String origFilename) {
		String[] splitDot = origFilename.split("\\.");
		String suffix = null;
		if (splitDot.length >= 2) {
			suffix = splitDot[splitDot.length - 1];
		}
		if (splitDot.length >= 1) {
			String nameBase = splitDot[0];
			String[] splitUnderscore = nameBase.split("_");
			String numberString = splitUnderscore[splitUnderscore.length - 1].replaceAll("\\D", "");
			try {
				int number = Integer.valueOf(numberString);
				String newFilename = filenameFormat.format(number);
				if (suffix != null) {
					newFilename += ("." + suffix.toLowerCase());
				}
				return newFilename;
			} catch (NumberFormatException e) {
				return null;
			}
		}
		return null;
	}

	public static FilenameFilter PdfFilter = new FilenameFilter() {
		@Override
		public boolean accept(File dir, String name) {
			boolean validImage = false;
			if (name.endsWith("pdf") || name.endsWith("PDF")) {
				validImage = true;
			}
			return validImage;
		}
	};
}
